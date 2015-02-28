-- TODO
-- Vocab needed
-- where
--   _a_ where _b_ -> no op?
-- set -> just a basic object
-- in
--   _symbol_ in _type=set_
--
-- tuple syntax ( , ). base it on , ?
--   ( _val1_ , _val2_ )  -> tuple
--   pre , post
--
-- and?
--
--
-- e.g.
-- def square: a square matrix is a n by n matrix.
-- def graph: a graph is a pair (V, E).
--   V is a set.
--   e in E is a (V, V).

module See.Primitives where
import See.Types
--import See.Definition
import See.Parse

import qualified Data.Map as M
import Control.Monad
import Control.Monad.State hiding (get, put)
import qualified Control.Monad.State as S (get, put)
import Control.Applicative ((<$>), (<*>))
import Data.Maybe (fromJust, mapMaybe)
import qualified Data.Traversable as T (Traversable, mapAccumR)
import Data.Foldable (Foldable)
import Text.Read (readMaybe)
import Debug.Trace (trace)

-- Primitive Rules --

tokenRule :: Tag -> Rule
tokenRule tag = do
  lit <- symbolLit tag
  nil <- store Nil
  return $ Subl {pre = nil, post = nil, output = Push lit}

definitionRule :: Rule
definitionRule = do
  (s, val) <- symbol

  pre <- storeList []
  marker <- symbolLit ":"
  post <- storeList [s, marker]

  return $ Subl {pre = pre, post = post, output = CreateFrame val}

qedRule :: Rule
qedRule = do
  nil <- store Nil
  return $ Subl {pre = nil, post = nil, output = CloseFrame}

-- Primitive Words --
-- a
--   a _type_        -> val
rule_a1 :: Rule
rule_a1 = do
  tlit <- store (Val "type")
  theType <- var
  propertyVal theType "type" tlit
  obj <- var
  propertyVal obj "type" theType
  pre <- storeList []
  post <- storeList [theType]
  return $ Subl {pre = pre, post = post, output = Push obj}

--   a _type_ _val_  -> val
rule_a2 :: Rule
rule_a2 = do
  tlit <- store (Val "type")
  theType <- var
  propertyVal theType "type" tlit
  obj <- var
  propertyVal obj "type" theType
  pre <- storeList []
  post <- storeList [theType, obj]
  return $ Subl {pre = pre, post = post, output = Push obj}
  
-- is
-- is, =
--   _val1_ is _val2_ -> unify val1 val2, return no object
rule_is :: Rule
rule_is = do
  lhs <- var
  rhs <- var
  unify lhs rhs
  pre <- storeList [lhs]
  post <- storeList [rhs]
  return $ Subl {pre = pre, post = post, output = DoNothing}

-- set
rule_set :: Rule
rule_set = do
  nil <- storeList []
  out <- store (Val "set")
  tlit <- store (Val "type")
  propertyVal out "type" tlit
  return $ Subl {pre = nil, post = nil, output = Push out}


-- TODO:
-- where
-- in
-- ( , )

-- Strange Rules --
-- syntactic pop
popRule :: Rule
popRule = do
  nil <- store Nil
  getlost <- var
  pre <- storeList [getlost]
  return $ Subl {pre = pre, post = nil, output = DoNothing}


-- Example Objects --
integerRule :: Integer -> Rule
integerRule i = do
  (obj, val) <- integer
  lit <- store $ IntLit i
  unify val lit
  nil <- store Nil
  return $ Subl {pre = nil, post = nil, output = Push obj}

matrixRule :: Rule
matrixRule = do
  (m, r, c) <- matrix
  by <- symbolLit "by"
  -- TODO parse `by` as a dimension object
  pre <- storeList [c, by, r]
  nil <- store Nil
  return $ Subl {pre = pre, post = nil, output = Push m}

tupleRule :: Rule
tupleRule = do
  a <- var
  b <- var
  pre <- storeList [b, a]
  post <- store Nil
  out <- store (Val "pair")
  first <- property out "first"
  second <- property out "second"
  unify a first
  unify b second
  return $ Subl {pre = pre, post = post, output = Push out}

mmulRule :: Rule
mmulRule = do
  -- Left, Right inputs
  (m1, r1, c1) <- matrix
  (m2, r2, c2) <- matrix
  -- Product matrix
  (mp, rp, cp) <- matrix

  unify c1 r2
  unify rp r1
  unify cp c2

  pre <- storeList [m1]
  post <- storeList [m2]

  return $ Subl {pre = pre, post = post, output = Push mp}

imulRule :: Rule
imulRule = do
  (i1, _) <- integer
  (i2, _) <- integer
  (out, _) <- integer

  pre <- storeList [i1]
  post <- storeList [i2]

  return $ Subl {pre = pre, post = post, output = Push out}

-- TODO make this right-biased; should reduce unnecessary ambiguity
parenRule :: Rule
parenRule = do
  body <- var
  right <- symbolLit ")"
  nil <- store Nil
  post <- storeList [body, right]
  return $ Subl {pre = nil, post = post, output = Push body}

-- Basic Parsers --

readInt :: String -> Maybe Integer
readInt = readMaybe

match :: String -> Rule -> Parser
match model rule str | model == str = Just rule
match _ _ _ = Nothing

intParse :: Parser
intParse word = do
  i <- readInt word
  return (integerRule i)

mmulParse :: Parser
mmulParse = match "*" mmulRule

imulParse :: Parser
imulParse = match "*" imulRule

tokenParse :: String -> Parser
tokenParse model = match model (tokenRule model)

matrixParse :: Parser
matrixParse = match "matrix" matrixRule

parenParse :: Parser
parenParse = match "(" parenRule

tupleParse :: Parser
tupleParse = match "pair" tupleRule

definitionParse :: Parser
definitionParse = match "def" definitionRule

-- Matches anything
symbolParse :: Parser
symbolParse sym = Just (symbolRule sym)

mainDictionary :: [Parser]
mainDictionary = [
  -- Stuff
  match "pop" popRule,

  -- basic nodes
  intParse,
  matrixParse,
    tokenParse "by",

  -- match "*"
  imulParse,
  mmulParse,

  -- grouping
  parenParse,
    tokenParse ")",

  -- pairs
  tupleParse,

  -- DEFINITIONS
  tokenParse ":",
  match "qed" qedRule,
  match "end" qedRule,
  definitionParse,

  -- Words
  match "a" rule_a1,
  match "a" rule_a2,
  match "is" rule_is,
  match "=" rule_is,
  match "set" rule_set
 ]

-- Main Parser Functions --
-- Special handling of '(' , ')'
tokenize :: String -> [String]
tokenize = words . concatMap pad
 where
   specialChars = "():="
   pad x | x `elem` specialChars = [' ', x, ' ']
   pad x = [x]

-- Returns parse stack
parse :: String -> VM Context
parse str =
  let stream = tokenize str in
  do 
   context <- initialContext
   --stack <- newVarStack
   --stack <- newStack
   mapM_ (parseWord context mainDictionary) stream
   return context


