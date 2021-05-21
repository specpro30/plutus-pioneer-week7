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

module Week07.EvenOdd -- implementation of Alice and Bob game. If sum of the two choices from both players is even then first player wins.  If sum is odd then the second player wins.
    ( Game (..)
    , GameChoice (..)
    , FirstParams (..)
    , SecondParams (..)
    , GameSchema
    , endpoints
    ) where

import           Control.Monad        hiding (fmap)
import           Data.Aeson           (FromJSON, ToJSON)
import qualified Data.Map             as Map
import           Data.Text            (Text)
import           GHC.Generics         (Generic)
import           Plutus.Contract      as Contract hiding (when)
import qualified PlutusTx
import           PlutusTx.Prelude     hiding (Semigroup(..), unless)
import           Ledger               hiding (singleton)
import           Ledger.Constraints   as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Ada           as Ada
import           Ledger.Value
import           Playground.Contract  (ToSchema)
import           Prelude              (Semigroup (..))
import qualified Prelude

data Game = Game
    { gFirst          :: !PubKeyHash    -- First player denoted by their public key hash
    , gSecond         :: !PubKeyHash    -- Second player denoted by their public key hash
    , gStake          :: !Integer       -- Stake in lovelaces used in game by each player
    , gPlayDeadline   :: !Slot          -- Deadline by which second player needs to make their move before first player can claim back their stake
    , gRevealDeadline :: !Slot          -- Second player has already made a move and first player must reveal their nonce before this deadline to claim their win 
    , gToken          :: !AssetClass    -- An arbitrary NFT that identifies the right instance of the UTXO for the game. We use Datum of UTXO sitting at script address of this contract to keep track of game 
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''Game

data GameChoice = Zero | One            -- Choices available for players 
    deriving (Show, Generic, FromJSON, ToJSON, ToSchema, Prelude.Eq, Prelude.Ord)

instance Eq GameChoice where            -- Need to define here Plutus Eq manually
    {-# INLINABLE (==) #-}              -- INLINABLE pragma for template haskell for the == operation 
    Zero == Zero = True                 
    One  == One  = True
    _    == _    = False                -- All other choice combinations returns False

PlutusTx.unstableMakeIsData ''GameChoice

data GameDatum = GameDatum ByteString (Maybe GameChoice)    -- GameDatum is used to keep track of State, ByteString is the hash that the first player submits, Maybe GameChoice is second player's move
                                                            -- Maybe is used since at the beginning second player hasn't made a move so it is 'Nothing'. After second player moves it becomes a 'Just'
    deriving Show

instance Eq GameDatum where
    {-# INLINABLE (==) #-}                                               -- INLINABLE pragma for template haskell for the == operation
    GameDatum bs mc == GameDatum bs' mc' = (bs == bs') && (mc == mc')    -- Two are equal if the ByteString hash (bs) and Maybe GameChoice (mc) are equal 

PlutusTx.unstableMakeIsData ''GameDatum

data GameRedeemer = Play GameChoice | Reveal ByteString | ClaimFirst | ClaimSecond    -- Play is when second player moves and argument is GameChoice (Play Zero or Play One)
                                                                                      -- Reveal happens when first player has won and shows the nonce (ByteString) as proof. No need to provide first player move
                                                                                      -- ClaimFirst is when second player doesn't make a move and first can claim back their stake
                                                                                      -- ClaimSecond is when the first player doesn't reveal cause they have lost and second player claim stake 
    deriving Show

PlutusTx.unstableMakeIsData ''GameRedeemer

{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer                 -- Given a Value extract the number of lovelaces contained in it 
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINABLE gameDatum #-}
gameDatum :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe GameDatum    -- given an output of a transaction (TxOut) and given a DatumHash Maybe get a Datum, return a Maybe GameDatum 
gameDatum o f = do
    dh      <- txOutDatum o                                            -- try to get a Datum Hash from output which may fail 
    Datum d <- f dh                                                    -- use the second argument fuction 'f' to turn the hash into a Datum value 
    PlutusTx.fromData d                                                -- try to pass this Datum value of something of the type gameDatum (same steps as Oracle in week 6)

{-# INLINABLE mkGameValidator #-}
mkGameValidator :: Game -> ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool  -- core business logic in the mkGameValidator function
                                                                                                           -- First argument is the parameter of Game type
                                                                                                           -- Second and Third argument are ByteStrings representing Zero and One since we can't use String Literals
                                                                                                           -- Then the usual Datume, Redeemer and Context of the Contract Monad 
mkGameValidator game bsZero' bsOne' dat red ctx =
    traceIfFalse "token missing from input" (assetClassValueOf (txOutValue ownInput) (gToken game) == 1) &&                    -- in all cases the own input that is being validated contains the state token 
    case (dat, red) of
        (GameDatum bs Nothing, Play c) ->                                                                                      -- first player has moved, second player (so far 'Nothing') now moves by chosing 'c' 
            traceIfFalse "not signed by second player"   (txSignedBy info (gSecond game))                                   && -- check to see that this move is made by second player by seeing if they signed tx  
            traceIfFalse "first player's stake missing"  (lovelaces (txOutValue ownInput) == gStake game)                   && -- check if first player has placed their stake 
            traceIfFalse "second player's stake missing" (lovelaces (txOutValue ownOutput) == (2 * gStake game))            && -- check if second player has placed their stake 
            traceIfFalse "wrong output datum"            (outputDatum == GameDatum bs (Just c))                             && -- The Datum has now changed from Nothing to Just c, since second player has moved 
            traceIfFalse "missed deadline"               (to (gPlayDeadline game) `contains` txInfoValidRange info)         && -- Check if the move by second player happens before first deadline 
            traceIfFalse "token missing from output"     (assetClassValueOf (txOutValue ownOutput) (gToken game) == 1)         -- NFT must be passed on to the new UTXO 

        (GameDatum bs (Just c), Reveal nonce) ->                                                                               -- Checks to see if first player has one by first player revealing the nonce 
            traceIfFalse "not signed by first player"    (txSignedBy info (gFirst game))                                    && -- check if first player has signed 
            traceIfFalse "commit mismatch"               (checkNonce bs nonce c)                                            && -- check to see if the nonce agrees with the hash (bs) submitted earlier
            traceIfFalse "missed deadline"               (to (gRevealDeadline game) `contains` txInfoValidRange info)       && -- check to see if all this is done before the deadline 
            traceIfFalse "wrong stake"                   (lovelaces (txOutValue ownInput) == (2 * gStake game))             && -- the input must contain the stake of both players 
            traceIfFalse "NFT must go to first player"   nftToFirst                                                            -- NFT goes back to the first player 

        (GameDatum _ Nothing, ClaimFirst) ->                                                                                   -- check if first player can get their stake back because second player not play 
            traceIfFalse "not signed by first player"    (txSignedBy info (gFirst game))                                    && -- check if signed by first player 
            traceIfFalse "too early"                     (from (1 + gPlayDeadline game) `contains` txInfoValidRange info)   && -- check if deadline has passed 
            traceIfFalse "first player's stake missing"  (lovelaces (txOutValue ownInput) == gStake game)                   && -- check if first player has provided their stake 
            traceIfFalse "NFT must go to first player"   nftToFirst                                                            -- NFT goes back to the first player 

        (GameDatum _ (Just _), ClaimSecond) ->                                                                                 -- both players have moved (Just _), first player realize lost or quit game 
            traceIfFalse "not signed by second player"   (txSignedBy info (gSecond game))                                   && -- check if second player has signed transaction  
            traceIfFalse "too early"                     (from (1 + gRevealDeadline game) `contains` txInfoValidRange info) && -- check if deadline has passed 
            traceIfFalse "wrong stake"                   (lovelaces (txOutValue ownInput) == (2 * gStake game))             && -- check if both players have provided their stake 
            traceIfFalse "NFT must go to first player"   nftToFirst                                                            -- NFT goes back to the first player 

        _                              -> False                                                                                -- in all other cases ('_') we fail the validation ('False')  
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx

    ownInput :: TxOut
    ownInput = case findOwnInput ctx of            -- This should never fail as we are validating the usage of a UTXO so there should always be an ownInput - the input of the UTXO we are presently validating 
        Nothing -> traceError "game input missing"
        Just i  -> txInInfoResolved i

    ownOutput :: TxOut                             -- If the game isn't over then there should be a new UTXO carrying the NFT with the updatd Datum 
    ownOutput = case getContinuingOutputs ctx of   -- Checks all the output that goes to the same address 
        [o] -> o                                   -- and only succeeds if it finds one such
        _   -> traceError "expected exactly one game output"

    outputDatum :: GameDatum
    outputDatum = case gameDatum ownOutput (`findDatum` info) of    -- makes use of the gameDatum and given that we have exactly one output at the script address it gives the game output datum 
        Nothing -> traceError "game output datum not found"         -- check fails or 
        Just d  -> d                                                -- succeeds and returns datum 

    checkNonce :: ByteString -> ByteString -> GameChoice -> Bool    -- in the case that the first player has won and wants to prove it by revealing the hash submitted at the beginning fits the nonce 
                                                                    -- First ByteString is the hash that was submitted, Second ByteString is the nonce, GameChoice is the move that both players made  
    checkNonce bs nonce cSecond = sha2_256 (nonce `concatenate` cFirst) == bs    -- cSecond is of type GameChoice and cFirst is of type ByteString 
                                                                                 -- the nonce is concatenated with cFirst and then hashed with sha2_256 
                                                                                 -- then it is checked to see if it is equal to the initial ByteString provided by first player (bs) 
      where
        cFirst :: ByteString     -- helper function used to convert cFirst into ByteString 
        cFirst = case cSecond of
            Zero -> bsZero'      -- if the choice is zero then we take the ByteString representing zero 
            One  -> bsOne'       -- if the choice is one then we take the ByteString representing one  

    nftToFirst :: Bool           -- as the first player had to provide the NFT at the beginning of the game, it only makes sense that the NFT is returned to first player at the end no matter who won the game 
    nftToFirst = assetClassValueOf (valuePaidTo info $ gFirst game) (gToken game) == 1    -- valuePaidTo gets all the info from the context of the pubKeyHash (gFirst) 
                                                                                          -- adds up all the values that go to that pubKeyHash in some output of the transaction 
                                                                                          -- this means that the first player will get the token 

data Gaming                                            -- boiler plate code to bundle the data types of Datum and Redeemer 
instance Scripts.ScriptType Gaming where
    type instance DatumType Gaming = GameDatum
    type instance RedeemerType Gaming = GameRedeemer

bsZero, bsOne :: ByteString                            -- define the ByteStrings (0 and 1) we will use. Note that this is completely arbitrary and we can use any two ByteString  
bsZero = "0"
bsOne  = "1"

gameInst :: Game -> Scripts.ScriptInstance Gaming      -- gameInst to compile the code which is parameterized by Game and the two ByteStrings (bsZero and bsOne). But since BS are provided there is only Game param
gameInst game = Scripts.validator @Gaming
    ($$(PlutusTx.compile [|| mkGameValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode game
        `PlutusTx.applyCode` PlutusTx.liftCode bsZero
        `PlutusTx.applyCode` PlutusTx.liftCode bsOne)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @GameDatum @GameRedeemer

gameValidator :: Game -> Validator                     -- boiler plate code for validator 
gameValidator = Scripts.validatorScript . gameInst

gameAddress :: Game -> Ledger.Address                  -- boiler plate code for address 
gameAddress = scriptAddress . gameValidator

findGameOutput :: HasBlockchainActions s => Game -> Contract w s Text (Maybe (TxOutRef, TxOutTx, GameDatum))    -- as preparation for off chain code we will need to find the UTXO that contains the NFT 
                                                                                                                -- Maybe returns the reference to the output (TxOutRef), the output itself (TxOutTx) and GameDatum 
findGameOutput game = do
    utxos <- utxoAt $ gameAddress game                                             -- get all the UTXO at the game address 
    return $ do                                                      
        (oref, o) <- find f $ Map.toList utxos                                     -- use the find function which finds an element in the list that satisfys predicate and returns a Just
                                                                                   -- after we have all the utxos we turn them into a list of pairs 
                                                                                   -- this will find the utxo that contains the token 
        dat       <- gameDatum (txOutTxOut o) (`Map.lookup` txData (txOutTxTx o))  -- use gameDatum to get the Datum to this UTXO 
        return (oref, o, dat)                                                      -- and then return the triple 
  where
    f :: (TxOutRef, TxOutTx) -> Bool
    f (_, o) = assetClassValueOf (txOutValue $ txOutTxOut o) (gToken game) == 1    -- take the pair and ignore the reference and get just the 'o' and check if the output contains the token 

-- now we have two contracts for the two players. one for the first player to play the game and the other for the second player to play the game. with corresponding parameters FirstParams and SecondParams 

data FirstParams = FirstParams
    { fpSecond         :: !PubKeyHash      -- Only need the second player here because the first player will be the owner of the wallet that invokes the contract (so their PubKeyHash is gotten automatically) 
    , fpStake          :: !Integer
    , fpPlayDeadline   :: !Slot
    , fpRevealDeadline :: !Slot
    , fpNonce          :: !ByteString      -- we need the nonce that the first player wants to use to conceal their choice 
    , fpCurrency       :: !CurrencySymbol  -- CS of the NFT 
    , fpTokenName      :: !TokenName       -- TN of the NFT 
    , fpChoice         :: !GameChoice      -- the move that the player wants to make (0 or 1) 
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

firstGame :: forall w s. HasBlockchainActions s => FirstParams -> Contract w s Text ()
firstGame fp = do
    pkh <- pubKeyHash <$> Contract.ownPubKey                                            -- first gets our own pubKeyHash
    let game = Game                                                                     -- define our parameters for the contract 
            { gFirst          = pkh                                                     -- assign our pubKeyHash to gFirst 
            , gSecond         = fpSecond fp                                             -- use the params we got from first params 
            , gStake          = fpStake fp
            , gPlayDeadline   = fpPlayDeadline fp
            , gRevealDeadline = fpRevealDeadline fp
            , gToken          = AssetClass (fpCurrency fp, fpTokenName fp)              -- assemble the NFT token CS and TN into the AssetClass 
            }
        v    = lovelaceValueOf (fpStake fp) <> assetClassValue (gToken game) 1          -- the stake and the NFT that we must put into the UTXO
        c    = fpChoice fp                                                              -- 'c' is our choice 
        bs   = sha2_256 $ fpNonce fp `concatenate` if c == Zero then bsZero else bsOne  -- bs is the hash of our choice. The nonce is concatenated with our choice of whether we want to play Zero or one 
        tx   = Constraints.mustPayToTheScript (GameDatum bs Nothing) v                  -- the contraints is simple, all we do is produce a script output at this address with GameDatum, bs and Nothing
                                                                                        -- (Nothing because player two has not played yet) and v 
    ledgerTx <- submitTxConstraints (gameInst game) tx                                  -- submit the tx 
    void $ awaitTxConfirmed $ txId ledgerTx                                             -- wait for transaction 
    logInfo @String $ "made first move: " ++ show (fpChoice fp)                         -- logs a message 

    void $ awaitSlot $ 1 + fpPlayDeadline fp                                            -- now second player has chance to move but need to do before the deadline. first player waits until deadline has passed 

    m <- findGameOutput game                                                            -- check to see if the UTXO contains the NFT 
    case m of
        Nothing             -> throwError "game output not found"                       -- throw an exception if NFT not found 
        Just (oref, o, dat) -> case dat of                                              -- normally we would find it so return the oref, o and dat 
            GameDatum _ Nothing -> do                                                   -- in this case the second player has not moved (Nothing) and the deadline has passed 
                logInfo @String "second player did not play"                            
                let lookups = Constraints.unspentOutputs (Map.singleton oref o) <>      -- as lookups we must provide the UTXO 
                              Constraints.otherScript (gameValidator game)              -- and provide the validator of the game 
                    tx'     = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData ClaimFirst)  -- ClaimFirst redeemer is invoked to get the first players stake back
                                                                                                              -- To do so we must spend this UTXO we found with this Redeemer 
                ledgerTx' <- submitTxConstraintsWith @Gaming lookups tx'
                void $ awaitTxConfirmed $ txId ledgerTx'
                logInfo @String "reclaimed stake"                                       -- logged that the stake was reclaimed 

            GameDatum _ (Just c') | c' == c -> do                                       -- in this case the second player has moved and choose the same choice as player one so second player loses
                logInfo @String "second player played and lost"                         -- logs that second player has lost 
                let lookups = Constraints.unspentOutputs (Map.singleton oref o)                                         <>  -- as lookups provide UTXO 
                              Constraints.otherScript (gameValidator game)                                                  -- and provide gameValidator 
                    tx'     = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData $ Reveal $ fpNonce fp) <>  -- use the Reveal $ fpNonce redeemer to claim the reward 
                              Constraints.mustValidateIn (to $ fpRevealDeadline fp)                                         -- submit this transaction before deadline 
                ledgerTx' <- submitTxConstraintsWith @Gaming lookups tx'                                                    -- submit the tx 
                void $ awaitTxConfirmed $ txId ledgerTx'                                                                    -- wait 
                logInfo @String "victory"                                                                                   -- log winning status 

            _ -> logInfo @String "second player played and won"                         -- in this case the second player has won so we don't do anything 

data SecondParams = SecondParams
    { spFirst          :: !PubKeyHash                      -- once again as the pubKeyHash of second player is gotten from the wallet we only need the first players pubKeyHash 
    , spStake          :: !Integer                         -- stake of the second player 
    , spPlayDeadline   :: !Slot                            -- 
    , spRevealDeadline :: !Slot
    , spCurrency       :: !CurrencySymbol
    , spTokenName      :: !TokenName
    , spChoice         :: !GameChoice                      -- don't need a nonce now cause the nonce is only used by first player to show their guess was indeed true 
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

secondGame :: forall w s. HasBlockchainActions s => SecondParams -> Contract w s Text ()
secondGame sp = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    let game = Game
            { gFirst          = spFirst sp
            , gSecond         = pkh
            , gStake          = spStake sp
            , gPlayDeadline   = spPlayDeadline sp
            , gRevealDeadline = spRevealDeadline sp
            , gToken          = AssetClass (spCurrency sp, spTokenName sp)
            }
    m <- findGameOutput game                                                                              -- tries to find the UTXO that contains the NFT for the game 
    case m of
        Just (oref, o, GameDatum bs Nothing) -> do                                                        -- and if we find it bs is hash of the commitment of the first player and Nothing since we haven't moved 
            logInfo @String "running game found"                                                          -- game is found 
            let token   = assetClassValue (gToken game) 1                                                 -- token is the NFT 
            let v       = let x = lovelaceValueOf (spStake sp) in x <> x <> token                         -- v is now the value of the two stakes ('in x <> x') of player one and two and also the NFT ('token')  
                c       = spChoice sp                                                                     -- 'c' is second players choice 
                lookups = Constraints.unspentOutputs (Map.singleton oref o)                            <>
                          Constraints.otherScript (gameValidator game)                                 <>
                          Constraints.scriptInstanceLookups (gameInst game)
                tx      = Constraints.mustSpendScriptOutput oref (Redeemer $ PlutusTx.toData $ Play c) <> -- 
                          Constraints.mustPayToTheScript (GameDatum bs $ Just c) v                     <>
                          Constraints.mustValidateIn (to $ spPlayDeadline sp)
            ledgerTx <- submitTxConstraintsWith @Gaming lookups tx
            let tid = txId ledgerTx
            void $ awaitTxConfirmed tid
            logInfo @String $ "made second move: " ++ show (spChoice sp)

            void $ awaitSlot $ 1 + spRevealDeadline sp

            m' <- findGameOutput game
            case m' of
                Nothing             -> logInfo @String "first player won"
                Just (oref', o', _) -> do
                    logInfo @String "first player didn't reveal"
                    let lookups' = Constraints.unspentOutputs (Map.singleton oref' o')                              <>
                                   Constraints.otherScript (gameValidator game)
                        tx'      = Constraints.mustSpendScriptOutput oref' (Redeemer $ PlutusTx.toData ClaimSecond) <>
                                   Constraints.mustValidateIn (from $ 1 + spRevealDeadline sp)                      <>
                                   Constraints.mustPayToPubKey (spFirst sp) token
                    ledgerTx' <- submitTxConstraintsWith @Gaming lookups' tx'
                    void $ awaitTxConfirmed $ txId ledgerTx'
                    logInfo @String "second player won"

        _ -> logInfo @String "no running game found"                                                         -- no game is found so we can't move and can't do anything 

type GameSchema = BlockchainActions .\/ Endpoint "first" FirstParams .\/ Endpoint "second" SecondParams

endpoints :: Contract () GameSchema Text ()
endpoints = (first `select` second) >> endpoints
  where
    first  = endpoint @"first"  >>= firstGame
    second = endpoint @"second" >>= secondGame
