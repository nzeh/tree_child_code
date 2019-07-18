{-# LANGUAGE TupleSections #-}

module Main where

import           Control.Monad (liftM, when)
import qualified Test.Matching
import qualified Test.Newick
import qualified Test.PQ
import           Test.QuickCheck
import           Test.QuickCheck.Test (isSuccess)
import qualified Test.Tree
import qualified Test.Util

main :: IO ()
main = runTestsAndSummarize [ Test.Util.tests
                            , Test.PQ.tests
                            , Test.Tree.tests
                            , Test.Matching.tests
                            , Test.Newick.tests
                            ]

-- Run a list of test suites and summarize the results of running them
runTestsAndSummarize :: [(String, [(String, Property)])] -> IO ()
runTestsAndSummarize suites = mapM runTests suites >>= summarizeResults

-- Run the tests in a test suite and return the list failed tests and the total
-- number of tests in the suite
runTests :: (String, [(String, Property)]) -> IO (String, ([String], Int))
runTests (suiteName, tests) = do putStrLn $ "*** RUNNING TEST SUITE " ++ suiteName ++ " ***"
                                 putStrLn ""
                                 results <- mapM (\test@(name, _) -> (name,) <$> runTest test) tests
                                 let failures = map fst $ filter (not . snd) results
                                 return (suiteName, (failures, length tests))

-- Summarize the results of running all suites.
summarizeResults :: [(String, ([String], Int))] -> IO ()
summarizeResults results = do summarizeSuites results
                              mapM_ summarizeTests results'
  where names    = map fst results
        len      = maximum (map length names)
        names'   = map (\n -> take len (n ++ repeat ' ')) names
        results' = zip names' (map snd results)

-- Summarize the number of suites run and the number and percentage of suites that passed all tests
summarizeSuites :: [(String, ([String], Int))] -> IO ()
summarizeSuites suites = putStrLn $ "Ran " ++ show total ++ " test suites, " ++
                                    fraction successes total ++ " successfully"
  where successes = length $ filter (null . fst . snd) suites
        total     = length $ suites

-- Summarize the tests in each suite.  List the number of tests in the suite, the number and percentage
-- of tests that passed, and list all tests that failed.
summarizeTests :: (String, ([String], Int)) -> IO ()
summarizeTests (suite, (failures, total)) = do putStrLn $ "  " ++ suite ++ " " ++
                                                          fraction (total - length failures) total
                                               when (not $ null failures) $
                                                 do putStrLn "    Failures"
                                                    mapM_ (\f -> putStrLn $ "      " ++ f) failures

-- Given a number of tests and a number of them that passed, format this information.
fraction :: Int -> Int -> String
fraction num denom = show num ++ "/" ++ show denom ++ " (" ++ show percent ++ "%)"
  where percent | denom == 0 = 100
                | otherwise  = 100 * num `div` denom

-- Run an individual test, returning True if the test passes and False otherwise
runTest :: (String, Property) -> IO Bool
runTest (name, test) = do putStrLn $ "=== " ++ name ++ " ==="
                          success <- isSuccess <$> quickCheckWithResult stdArgs { maxSuccess = 100 } test
                          putStrLn ""
                          return success
