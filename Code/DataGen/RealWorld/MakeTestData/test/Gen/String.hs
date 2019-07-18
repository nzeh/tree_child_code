module Gen.String ( AlNum(..)
                  ) where

import Test.QuickCheck

-- Random alphanumeric string
newtype AlNum = AlNum { getAlNum :: String }
              deriving Show

instance Arbitrary AlNum where
  arbitrary = AlNum <$> listOf (elements $ ['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z'])
