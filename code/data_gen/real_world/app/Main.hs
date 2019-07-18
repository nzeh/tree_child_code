module Main where

import Control.Monad ((>=>))
import ExtractTrees
import Newick
import System.Environment (getArgs)
import Tree (Tree)

-- Main function
main :: IO ()
main = do args <- getArgs
          case args of
            [leafCount, inFile, outFile] 
              | Just leafCt <- parseArg leafCount -> run leafCt inFile outFile
            _                                     -> usage

-- Command line parser
parseArg :: Read t => String -> Maybe t
parseArg argStr | [(arg, "")] <- reads argStr = Just arg
                | otherwise                   = Nothing

-- Usage message
usage :: IO ()
usage = putStrLn "USAGE: MakeTestData <leaf count> <input file> <output file>"

-- Run the generator
run :: Int -> String -> String -> IO ()
run leafCount inFile outFile = readFile inFile
                           >>= treesFromNewickLogging inFile
                           >>= either (putStrLn . show) (extractTrees leafCount >=> uncurry (reportResults outFile))

-- Report the results: Write the generated trees to the given output file and print
-- basic states to the screen
reportResults :: String -> Stats -> [Tree String] -> IO ()
reportResults outFile stats trees = do writeFile outFile (asNewick trees)
                                       printStats stats

-- Print the basic states
printStats :: Stats -> IO ()
printStats stats = do pr "Number of input trees:               " numInTrees
                      pr "Number of input labels:              " numInLabels
                      pr "Number of output trees:              " numOutTrees
                      pr "Number of output labels:             " numOutLabels
                      pr "Number of resolved multifurcations:  " numMultifurcations
                      pr "Minimum output node degree:          " minNodeDegree
                      pr "Maximum output node degree:          " maxNodeDegree
                      pr "Output trees have chosen label set:  " labelSetOk
                      pr "Output trees are valid restrictions: " restrictionsOk
  where pr label stat = putStrLn $ label ++ show (stat stats)

-- Format a Boolean as OK/FAIL
formatBool :: Bool -> String
formatBool True  = "OK"
formatBool False = "FAIL"
