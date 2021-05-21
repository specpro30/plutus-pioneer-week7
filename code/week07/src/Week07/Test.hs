{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Week07.Test where                                    -- Testing of Alice and Bob game using emulator trace Monad 

import           Control.Monad              hiding (fmap)
import           Control.Monad.Freer.Extras as Extras
import           Data.Default               (Default (..))
import qualified Data.Map                   as Map
import           Ledger
import           Ledger.Value
import           Ledger.Ada                 as Ada
import           Plutus.Trace.Emulator      as Emulator
import           PlutusTx.Prelude
import           Wallet.Emulator.Wallet

import           Week07.EvenOdd

test :: IO ()                                                         -- in test function all four cominations of GameChoice are run in sequence 
test = do
    test' Zero Zero
    test' Zero One
    test' One Zero
    test' One One

test' :: GameChoice -> GameChoice -> IO ()                            -- parameterized by two GameChoice one for player one and the other for player two 
test' c1 c2 = runEmulatorTraceIO' def emCfg $ myTrace c1 c2
  where
    emCfg :: EmulatorConfig                                           -- specify the inital distribution of funds for wallets 
    emCfg = EmulatorConfig $ Left $ Map.fromList
        [ (Wallet 1, v <> assetClassValue (AssetClass (gameTokenCurrency, gameTokenName)) 1)  -- provide wallet 1 with the NFT using the emulatorConfig to mint for testing purposes only  
        , (Wallet 2, v)
        ]

    v :: Value
    v = Ada.lovelaceValueOf 1000_000_000

gameTokenCurrency :: CurrencySymbol
gameTokenCurrency = "ff"                                              -- make up currency symbol and. In real production code we would need to really mint the NFT using the forgeContract from Currency use case
                                                                      -- or using our own contract from the minting policy lecture

gameTokenName :: TokenName
gameTokenName = "STATE TOKEN"                                         -- some arbitrary token name 

myTrace :: GameChoice -> GameChoice -> EmulatorTrace ()
myTrace c1 c2 = do                                                    -- give myTrace two parameters c1 and c2 (choice one and choice two) 
    Extras.logInfo $ "first move: " ++ show c1 ++ ", second move: " ++ show c2

    h1 <- activateContractWallet (Wallet 1) endpoints                 -- start instance for endpoints contract for wallet one 
    h2 <- activateContractWallet (Wallet 2) endpoints                 -- start instance for endpoints contract for wallet two 

    let pkh1 = pubKeyHash $ walletPubKey $ Wallet 1                   -- look up the pubKeyHash of two wallets 
        pkh2 = pubKeyHash $ walletPubKey $ Wallet 2

        fp = FirstParams                                              -- define the parameters for first and second players (first player is wallet 1, second player is wallet 2)
                { fpSecond         = pkh2
                , fpStake          = 5000000                          -- stake is 5 ADA
                , fpPlayDeadline   = 5                                -- playdeadline is 5 slots
                , fpRevealDeadline = 10                               -- revealdeadline is 10 slots 
                , fpNonce          = "SECRETNONCE"                    -- in reality this should be a random string but for testing we use "SECRETNONCE" 
                , fpCurrency       = gameTokenCurrency                -- tokens forged using emulatorConfig as the NFT 
                , fpTokenName      = gameTokenName
                , fpChoice         = c1
                }
        sp = SecondParams
                { spFirst          = pkh1
                , spStake          = 5000000
                , spPlayDeadline   = 5
                , spRevealDeadline = 10
                , spCurrency       = gameTokenCurrency
                , spTokenName      = gameTokenName
                , spChoice         = c2
                }

    callEndpoint @"first" h1 fp                                       -- call the first endpoint on wallet 1 with the fp parameters 

    void $ Emulator.waitNSlots 3                                      -- wait 3 slots 

    callEndpoint @"second" h2 sp                                      -- then call the second endpoint on wallet 2 with the sp parameters 

    void $ Emulator.waitNSlots 10                                     -- then wait 10 slots 
