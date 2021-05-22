{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Week07.StateMachine                   -- State Machine implementation of Alice and Bob game 
    ( Game (..)
    , GameChoice (..)
    , FirstParams (..)
    , SecondParams (..)
    , GameSchema
    , endpoints
    ) where

import           Control.Monad                hiding (fmap)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Text                    (Text, pack)
import           GHC.Generics                 (Generic)
import           Plutus.Contract              as Contract hiding (when)
import           Plutus.Contract.StateMachine
import qualified PlutusTx
import           PlutusTx.Prelude             hiding (Semigroup(..), check, unless)
import           Ledger                       hiding (singleton)
import           Ledger.Ada                   as Ada
import           Ledger.Constraints           as Constraints
import           Ledger.Typed.Tx
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Value
import           Playground.Contract          (ToSchema)
import           Prelude                      (Semigroup (..))
import qualified Prelude

data Game = Game
    { gFirst          :: !PubKeyHash
    , gSecond         :: !PubKeyHash
    , gStake          :: !Integer
    , gPlayDeadline   :: !Slot
    , gRevealDeadline :: !Slot
    , gToken          :: !AssetClass
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''Game

data GameChoice = Zero | One
    deriving (Show, Generic, FromJSON, ToJSON, ToSchema, Prelude.Eq, Prelude.Ord)

instance Eq GameChoice where
    {-# INLINABLE (==) #-}
    Zero == Zero = True
    One  == One  = True
    _    == _    = False

PlutusTx.unstableMakeIsData ''GameChoice

data GameDatum = GameDatum ByteString (Maybe GameChoice) | Finished    -- added constructor Finished to reflect the final state of the State Machine 
                                                                       -- as before the ByteString is the hash provided by the first player and the GameChoice is the move made by second player 
    deriving Show

instance Eq GameDatum where
    {-# INLINABLE (==) #-}
    GameDatum bs mc == GameDatum bs' mc' = (bs == bs') && (mc == mc')
    Finished        == Finished          = True                        -- added a Eq statement for the Finished state 
    _               == _                 = False

PlutusTx.unstableMakeIsData ''GameDatum

data GameRedeemer = Play GameChoice | Reveal ByteString | ClaimFirst | ClaimSecond
    deriving Show

PlutusTx.unstableMakeIsData ''GameRedeemer

{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINABLE gameDatum #-}
gameDatum :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe GameDatum
gameDatum o f = do
    dh      <- txOutDatum o
    Datum d <- f dh
    PlutusTx.fromData d

{-# INLINABLE transition #-}
transition :: Game -> State GameDatum -> GameRedeemer -> Maybe (TxConstraints Void Void, State GameDatum)              -- the transition function of the state machine which sort of corresponds to 
                                                                                                                       -- the mkGameValidator from EvenOdd.hs
                                                                                                                       -- takes Game as a parameter, State s i (s=GameDatum, i=GameRedeemer)
                                                                                                                       -- Maybe (TxConstraints=constraints that need to be met, State GameDatum=the new State)
transition game s r = case (stateValue s, stateData s, r) of                                                           -- stateValue s is the value in the UTXO we are consuming, stateData s is the Datum,
                                                                                                                       -- r is the Redeemer 
    (v, GameDatum bs Nothing, Play c)
        | lovelaces v == gStake game         -> Just ( Constraints.mustBeSignedBy (gSecond game)                    <> -- check that v (value) is the stake of the game. Result of the transition funcion is 'Just'
                                                                                                                       -- check two contraints, then the new State with new Datum (GameDatum)
                                                                                                                       -- and Value (lovelaceValueOf)
                                                       Constraints.mustValidateIn (to $ gPlayDeadline game)            -- notice that we don't mention NFT here because the State Machine takes care of it 
                                                     , State (GameDatum bs $ Just c) (lovelaceValueOf $ 2 * gStake game)
                                                     )
    (v, GameDatum _ (Just _), Reveal _)                                                                                -- check that v (value) now contains stake from both players 
        | lovelaces v == (2 * gStake game)   -> Just ( Constraints.mustBeSignedBy (gFirst game)                     <> -- nonce is not checked here because Contraints can't handle nonce checking 
                                                       Constraints.mustValidateIn (to $ gRevealDeadline game)       <>
                                                       Constraints.mustPayToPubKey (gFirst game) token                 -- check that NFT must go back to first player 
                                                     , State Finished mempty                                           -- game is finished 
                                                     )
    (v, GameDatum _ Nothing, ClaimFirst)                                                                               -- case for second player not playing and first player reclaims 
        | lovelaces v == gStake game         -> Just ( Constraints.mustBeSignedBy (gFirst game)                     <> -- check that the value (v) input from first player is correct and first player signed 
                                                       Constraints.mustValidateIn (from $ 1 + gPlayDeadline game)   <> -- check that the PlayDeadline has passed 
                                                       Constraints.mustPayToPubKey (gFirst game) token                 -- gives the NFT back to first player 
                                                     , State Finished mempty                                           -- finish game 
                                                     )
    (v, GameDatum _ (Just _), ClaimSecond)                                                                             -- first player losses or quits and second player claims winnings
        | lovelaces v == (2 * gStake game)   -> Just ( Constraints.mustBeSignedBy (gSecond game)                    <> -- check v contains both players stakes. check second player has signed 
                                                       Constraints.mustValidateIn (from $ 1 + gRevealDeadline game) <> -- check RevealDeadlins has passed 
                                                       Constraints.mustPayToPubKey (gFirst game) token                 -- NFT is given back to first player 
                                                     , State Finished mempty                                           -- game is finished 
                                                     )
    _                                        -> Nothing                                                                -- all other states with arbitrary transitions are in valid 
  where
    token :: Value                                                 -- helper function to define the NFT 
    token = assetClassValue (gToken game) 1

{-# INLINABLE final #-}
final :: GameDatum -> Bool
final Finished = True         -- definition of the final state of the state machine 
final _        = False        -- everything else is false 

{-# INLINABLE check #-}
check :: ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool     -- nonce check. similar to previous file EvenOdd.hs  
check bsZero' bsOne' (GameDatum bs (Just c)) (Reveal nonce) _ =                             -- second player has played (Just c) and redeemer is 'reveal nonce'
    sha2_256 (nonce `concatenate` if c == Zero then bsZero' else bsOne') == bs              -- nonce check is similar to previous file EvenOdd.hs 
check _       _      _                       _              _ = True                        -- in all other situations we don't need an additional check so can return true 

{-# INLINABLE gameStateMachine #-}
gameStateMachine :: Game -> ByteString -> ByteString -> StateMachine GameDatum GameRedeemer -- definition of state machine 
gameStateMachine game bsZero' bsOne' = StateMachine
    { smTransition  = transition game                                                       -- these four fields are defined above 
    , smFinal       = final
    , smCheck       = check bsZero' bsOne'
    , smThreadToken = Just $ gToken game                                                    -- thread token is just taken from the 'game' value 
    }

{-# INLINABLE mkGameValidator #-}
mkGameValidator :: Game -> ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
mkGameValidator game bsZero' bsOne' = mkValidator $ gameStateMachine game bsZero' bsOne'    -- mkValidator turns gameStateMachine to the type defined in above line which is same 

type Gaming = StateMachine GameDatum GameRedeemer                                           -- bundle datum type and redeemer type for the state machine

bsZero, bsOne :: ByteString
bsZero = "0"
bsOne  = "1"

gameStateMachine' :: Game -> StateMachine GameDatum GameRedeemer                            -- don't understand why we need this. is this for the off chain code?
gameStateMachine' game = gameStateMachine game bsZero bsOne                                 -- don't need the two ByteString params for the offchain code 

gameInst :: Game -> Scripts.ScriptInstance Gaming                                           -- same as code in EvenOdd.hs 
gameInst game = Scripts.validator @Gaming
    ($$(PlutusTx.compile [|| mkGameValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode game
        `PlutusTx.applyCode` PlutusTx.liftCode bsZero
        `PlutusTx.applyCode` PlutusTx.liftCode bsOne)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @GameDatum @GameRedeemer

gameValidator :: Game -> Validator
gameValidator = Scripts.validatorScript . gameInst

gameAddress :: Game -> Ledger.Address
gameAddress = scriptAddress . gameValidator

gameClient :: Game -> StateMachineClient GameDatum GameRedeemer                                         -- gameClient is a StateMachineClient and is used to interact with StateMachine from wallet 
gameClient game = mkStateMachineClient $ StateMachineInstance (gameStateMachine' game) (gameInst game)  -- to get the mkStateMachineClient we first create a StateMachineInstance that bundles 
                                                                                                        -- the state machine (gameStateMachine) with the script instance (gameInst) of the state machine
                                                                                                        -- this then creates the gameClient used by the wallet 

data FirstParams = FirstParams                                -- First Params are the same as EvenOdd.hs 
    { fpSecond         :: !PubKeyHash
    , fpStake          :: !Integer
    , fpPlayDeadline   :: !Slot
    , fpRevealDeadline :: !Slot
    , fpNonce          :: !ByteString
    , fpCurrency       :: !CurrencySymbol
    , fpTokenName      :: !TokenName
    , fpChoice         :: !GameChoice
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

mapError' :: Contract w s SMContractError a -> Contract w s Text a  
mapError' = mapError $ pack . show                                    -- need to show the SMContractError and then packing it to turn it into a text error message instead of the SMContractError type 

firstGame :: forall w s. HasBlockchainActions s => FirstParams -> Contract w s Text ()
firstGame fp = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    let game   = Game
            { gFirst          = pkh
            , gSecond         = fpSecond fp
            , gStake          = fpStake fp
            , gPlayDeadline   = fpPlayDeadline fp
            , gRevealDeadline = fpRevealDeadline fp
            , gToken          = AssetClass (fpCurrency fp, fpTokenName fp)
            }
        client = gameClient game                                                            -- now we define client as gameClient to interact with StateMachine from off chain 
        v      = lovelaceValueOf (fpStake fp)
        c      = fpChoice fp
        bs     = sha2_256 $ fpNonce fp `concatenate` if c == Zero then bsZero else bsOne
    void $ mapError' $ runInitialise client (GameDatum bs Nothing) v                        -- we need to then runInitialise to start the state machine that creates a UTXO at the state machine address 
                                                                                            -- takes client as the first argument and the intial Datum and Value in the UTXO sitting at that address 
                                                                                            -- this will automagicall put the NFT there as well so we only have to specify the stake that first player puts there 
    logInfo @String $ "made first move: " ++ show (fpChoice fp)

    void $ awaitSlot $ 1 + fpPlayDeadline fp

    m <- mapError' $ getOnChainState client                                                 -- now we need to find the UTXO after the second player has moved and we do this by 'getOnChainState client'
    case m of
        Nothing             -> throwError "game output not found"                           -- throw error if not found 
        Just ((o, _), _) -> case tyTxOutData o of                                           -- use the tyTxOutData to directly access the Datum (this is a lot simplier then before) 

            GameDatum _ Nothing -> do                                                       -- second player hasn't moved and first player can reclaim their stake 
                logInfo @String "second player did not play"
                void $ mapError' $ runStep client ClaimFirst                                -- runStep (taking ClaimFirst redeemer) creates a transaction and submits it which will transition the state machine 
                logInfo @String "first player reclaimed stake"                              -- this saves a lot of work because runStep uses all the contraints in the transition function 

            GameDatum _ (Just c') | c' == c -> do                                           -- this case is when the second player has moved and first player has won 
                logInfo @String "second player played and lost"
                void $ mapError' $ runStep client $ Reveal $ fpNonce fp                     -- using runStep again first player reveals their nonce to claim victory
                logInfo @String "first player revealed and won"                             -- (no constraints, lookups or helper functions needed here as well since runStep takes care of it) 
                                                                                            -- using the state machine method, the on-chain code now validates and constructs of the transaction
            _ -> logInfo @String "second player played and won"

data SecondParams = SecondParams
    { spFirst          :: !PubKeyHash
    , spStake          :: !Integer
    , spPlayDeadline   :: !Slot
    , spRevealDeadline :: !Slot
    , spCurrency       :: !CurrencySymbol
    , spTokenName      :: !TokenName
    , spChoice         :: !GameChoice
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

secondGame :: forall w s. HasBlockchainActions s => SecondParams -> Contract w s Text ()
secondGame sp = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    let game   = Game
            { gFirst          = spFirst sp
            , gSecond         = pkh
            , gStake          = spStake sp
            , gPlayDeadline   = spPlayDeadline sp
            , gRevealDeadline = spRevealDeadline sp
            , gToken          = AssetClass (spCurrency sp, spTokenName sp)
            }
        client = gameClient game
    m <- mapError' $ getOnChainState client
    case m of
        Nothing          -> logInfo @String "no running game found"
        Just ((o, _), _) -> case tyTxOutData o of
            GameDatum _ Nothing -> do                                         -- this case is we haven't played yet so we should play 
                logInfo @String "running game found"
                void $ mapError' $ runStep client $ Play $ spChoice sp        -- use runStep and play with our spChoice sp redeemer 
                logInfo @String $ "made second move: " ++ show (spChoice sp)

                void $ awaitSlot $ 1 + spRevealDeadline sp                    -- wait for deadline to pass 

                m' <- mapError' $ getOnChainState client                      -- check the new state again 
                case m' of
                    Nothing -> logInfo @String "first player won"             -- if there is none it means the first player had won 
                    Just _  -> do                                             -- if there is a new state then first player hasn't won 
                        logInfo @String "first player didn't reveal"
                        void $ mapError' $ runStep client ClaimSecond         -- so the second player wins and can claim the stake of player one and player two
                        logInfo @String "second player won"

            _ -> throwError "unexpected datum"                                -- all other cases are unexpected 

type GameSchema = BlockchainActions .\/ Endpoint "first" FirstParams .\/ Endpoint "second" SecondParams

endpoints :: Contract () GameSchema Text ()
endpoints = (first `select` second) >> endpoints
  where
    first  = endpoint @"first"  >>= firstGame
    second = endpoint @"second" >>= secondGame
