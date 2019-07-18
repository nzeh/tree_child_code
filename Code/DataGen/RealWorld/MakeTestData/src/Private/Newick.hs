{-# LANGUAGE FlexibleContexts, TypeFamilies #-}

module Private.Newick where

import           Control.Monad.IO.Class (liftIO)
import           Control.Monad (void)
import qualified Data.Set as S
import           Text.Parsec
import           Tree

-- Parse a multi-line Newick string into a collection of trees, one per line.
-- Log the progress
treesFromNewickLogging :: String -> String -> IO (Either ParseError [Tree String])
treesFromNewickLogging = runParserT (endBy loggingParser endOfLine <* loggingEnd) 0
  where loggingParser = do tree  <- treeP
                           count <- getState
                           liftIO (putStr $ "\rParsing input trees: " ++ show count)
                           putState (count + 1)
                           return tree
        loggingEnd = eof >> liftIO (putStrLn "")

-- Parse a multi-line Newick string into a collection of trees, one per line
treesFromNewick :: String -> String -> Either ParseError [Tree String]
treesFromNewick = parse (endBy1 treeP endOfLine <* eof)

-- Parse a one-line Newick string into a tree
treeFromNewick :: String -> String -> Either ParseError (Tree String)
treeFromNewick = parse (treeP <* eof)

-- Parser transformer
type P = ParsecT String

-- Tree parser
treeP :: Monad m => P s m (Tree String)
treeP = subtreeP <* char ';'

-- Subtree parser
subtreeP :: Monad m => P s m (Tree String)
subtreeP = nodeP <* optional edgeLengthP

-- Node parser
nodeP :: Monad m => P s m (Tree String)
nodeP = internalNodeP <|> leafP

-- Internal node parser
internalNodeP :: Monad m => P s m (Tree String)
internalNodeP = Node . S.fromList <$> between (char '(') (char ')')
                                              (subtreeP `sepBy1` char ',') <* optional (void labelP)

-- Leaf parser
leafP :: Monad m => P s m (Tree String)
leafP = Leaf <$> labelP

-- Label parser
labelP :: Monad m => P s m String
labelP = many1 (noneOf ":,();\n")

-- Edge length parser (We need to be able to parse them even though we ignore them).
edgeLengthP :: Monad m => P s  m ()
edgeLengthP = char ':' >> void numberP

-- Number parser
numberP :: Monad m => P s m Double
numberP = do sign     <- maybe "" (: "") <$> optionMaybe (char '-')
             intPart  <- many1 digit
             fracPart <- option "" ((:) <$> char '.' <*> many1 digit)
             return (read $ sign ++ intPart ++ fracPart)

-- Things that can be converted to Newick format
class AsNewick t where
  type LabelType t :: *
  asNewickWith :: (LabelType t -> String) -> t -> String

instance AsNewick (Tree t) where
  type LabelType (Tree t) = t
  asNewickWith formatLeaf tree = formatTree formatLeaf tree ";"

instance AsNewick t => AsNewick [t] where
  type LabelType [t] = LabelType t
  asNewickWith formatLeaf = unlines . map (asNewickWith formatLeaf)

asNewick :: (AsNewick t, Show (LabelType t)) => t -> String
asNewick = asNewickWith show

-- Format a subtree
formatTree :: (t -> String) -> Tree t -> String -> String
formatTree formatLeaf = go
  where go (Leaf x)  rest = formatLeaf x ++ rest
        go (Node cs) rest = '(' : go c (foldr goSibling (')' : rest) cs')
          where c:cs' = S.elems cs
        goSibling tree rest = ',' : go tree rest
