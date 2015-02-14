-- TODO
--  print output graph
--  split up this file
--  web client
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module See.Types where

import qualified Data.Map as M
import Control.Monad
import Control.Monad.State hiding (get, put)
import qualified Control.Monad.State as S (get, put)
import Control.Applicative ((<$>))
import Data.Maybe (fromJust, mapMaybe)
import qualified Data.Traversable as T (Traversable, mapAccumR)
import Data.Foldable (Foldable)
import Text.Read (readMaybe)
import Debug.Trace (trace)

-- Environment stuff
-- TODO merge with Name package
newtype Name = N Integer
 deriving (Eq, Ord)

instance Show Name where
  show (N i) = "#" ++ show i

type UState a = (Integer, M.Map Name a)
emptyChain :: UState a
emptyChain = (0, M.empty)

type UM a = StateT (UState a) [] 
runUM :: UM s a -> [(a, UState s)]
runUM m = runStateT m emptyChain

get :: Name -> UM a a
get name = do
  (_, m) <- S.get
  return $ fromJust . M.lookup name $ m

store :: a -> UM a Name
store val = do
  (count, env) <- S.get
  let name = N (count + 1)
  S.put (count + 1, M.insert name val env)
  return name

put :: Name -> a -> UM a ()
put name val = modify $ \(c, env) -> (c, M.insert name val env)

-- Returns all objects that refer to given name
refs :: (Name -> a -> Maybe b) -> UM a [b]
refs fn = do
  (_, env) <- S.get
  return $ mapMaybe (uncurry fn) $ M.toList env

modifyAll :: (Name -> a -> a) -> UM a ()
modifyAll fn = do
  (c, env) <- S.get
  S.put (c, M.mapWithKey fn env)

getEnv :: UM a [(Name, a)]
getEnv = M.toList . snd <$> S.get

--------------
-- Our Data --
--------------
type Tag = String

-- Used to represent object properties
-- [root]'s [tag] property is [object]
data Link a = Link
  { tag :: Tag
  , root :: a
  , object :: a
  }
 deriving (Eq, Ord, Show, Functor, Foldable, T.Traversable)

-- "preconditions", "postconditions", resultant object
data Subl a = Subl
  { pre :: [a]
  , post :: [a]
  , output :: a
  }
 deriving (Eq, Ord, Show, Functor, Foldable, T.Traversable)

data Val a = Val Tag [a]
           | Prop (Link a)
           | Sub (Subl a)
           | Var
           -- Stacks are basic
           | Nil
           | Cons a a
           | Ptr a
           -- Literals
           | IntLit Integer
           | Symbol Tag
  deriving (Eq, Ord, Show, Functor, Foldable, T.Traversable)

newtype Stack = Stack Name
  deriving (Show, Eq, Ord)

-- Primary monad type
type VM = UM (Val Name)

-- Basic objects, Property Utilities --
var :: VM Name
var = store Var

property :: Name -> Tag -> VM Name
property name tag = do
  obj <- var
  _ <- store $ Prop (Link {tag = tag, root = name, object = obj})
  return obj

properties :: Name -> VM [Link Name]
properties root = do
  refs isProp
 where
  isProp _ (Prop l@(Link {root = r})) | r == root = Just l
  isProp _ _ = Nothing

getProperty :: Name -> Tag -> VM Name
getProperty name tag = do
  ps <- properties name
  -- Failure kills the branch
  [val] <- return $ mapMaybe select ps
  return val
 where
   select (Link {tag = t, object = o}) | t == tag = Just o
   select _ = Nothing

setProperty :: Name -> Tag -> Name -> VM ()
setProperty name tag val = do
  p <- getProperty name tag
  unify p val

symbol :: Tag -> VM Name
symbol tag = store (Symbol tag)

pair :: VM (Name, Name, Name)
pair = do
 head <- var
 tail <- var
 p <- store (Cons head tail)
 return (p, head, tail)

-- Elementary Objects, Rules --
type Rule = VM (Subl Name)

-- Current pattern:
--   an object type is a VM action that returns a tuple of Names
--     first -> Val representing object
--     each other -> a property
--   this makes it easy to immediately impose relations on properties
--   see mmulRule below for example

integer :: VM (Name, Name)
integer = do
  i <- store (Val "integer" [])
  val <- property i "value"
  return (i, val)

integerRule :: Integer -> Rule
integerRule i = do
  (obj, val) <- integer
  lit <- store $ IntLit i
  unify val lit
  return $ Subl {pre = [], post = [], output = obj}

matrix :: VM (Name, Name, Name)
matrix = do
  m <- store (Val "matrix" [])
  rows <- property m "rows"
  columns <- property m "columns"
  return (m, rows, columns)

matrixRule :: Rule
matrixRule = do
  (m, r, c) <- matrix
  by <- symbol "by"
  -- TODO parse `by` as a dimension object
  return $ Subl {pre = [c, by, r], post = [], output = m}

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

  return $ Subl {pre = [m1], post = [m2], output = mp}

imulRule :: Rule
imulRule = do
  (i1, _) <- integer
  (i2, _) <- integer
  (out, _) <- integer

  return $ Subl {pre = [i1], post = [i2], output = out}

tokenRule :: Tag -> Rule
tokenRule tag = do
  t <- store (Symbol tag)
  return $ Subl {pre = [], post = [], output = t}

parenRule :: Rule
parenRule = do
  body <- var
  right <- symbol ")"
  return $ Subl {pre = [], post = [body, right], output = body}

-- Rule Simplification
bindLeft :: Name -> Subl Name -> VM (Subl Name)
bindLeft name (Subl (x : xs) rs out) = do
  unify name x
  return $ Subl xs rs out
bindLeft a b = error $ "bindLeft. " ++ sep a b

bindRight :: Name -> Subl Name -> VM (Subl Name)
bindRight name (Subl ls (x : xs) out) = do
  unify name x
  return $ Subl ls xs out
bindRight a b = error $ "bindLeft. " ++ sep a b

reduceLeft :: Stack -> Subl Name -> VM (Subl Name)
reduceLeft _ s@(Subl [] _ _) = return s
reduceLeft stack sub = do
  top <- pop stack
  sub' <- bindLeft top sub
  reduceLeft stack sub'

-- Debugging
debugFlag :: Bool
debugFlag = False

sep :: (Show a, Show b) => a -> b -> String
sep s1 s2 = show s1 ++ ", " ++ show s2

printError :: String -> VM ()
printError msg = do
  env <- getEnv
  trace ("\n\nERROR\n\n" ++ msg ++ "\n\n" ++ unlines (map show env)) $ return ()

-- Unification
assert :: Bool -> String -> VM ()
assert cond msg = if cond then return () else do
  -- This is noisy since it prints for every failed branch
  if debugFlag
    then printError msg
    else return ()
  mzero

unify :: Name -> Name -> VM ()
unify n1 n2 = do
  v1 <- get n1
  v2 <- get n2
  -- Unify values
  unifyLeft n1 v1 n2 v2
  -- Unify all properties
  unifyProperties n1 n2

-- Properties are treated as extra knowledge about an object
-- When two objects are unified, their properties are taken together as a union
-- A property can cause unification failure only if it is present for both
--   objects with conflicting values
-- An object should have at most one value for a property, although the graph
--   does not maintain this invariant
unifyProperties :: Name -> Name -> VM ()
unifyProperties left right = do
  leftProps <- properties left
  rightProps <- properties right
  mapM_ (\l -> unifyProperty left l) rightProps
  mapM_ (\l -> unifyProperty right l) leftProps

lookupWith :: Eq b => (a -> b) -> b -> [a] -> Maybe a
lookupWith _ _ [] = Nothing
lookupWith f key (x : xs) =
  if f x == key then Just x else lookupWith f key xs

unifyProperty :: Name -> Link Name -> VM ()
unifyProperty name prop = do
  props <- properties name
  case lookupWith tag (tag prop) props of
    -- Add the new property
    Nothing -> store (Prop (prop {root = name})) >> return ()
    -- Or unify with the existing one
    Just link -> unify (object link) (object prop)

unifyLeft :: Name -> Val Name -> Name -> Val Name -> VM ()
unifyLeft n1 Var n2 Var =
  substitute n1 n2
unifyLeft n1 Var _ v2 = do
  put n1 v2
unifyLeft n1 v1 n2 Var = unifyLeft n2 Var n1 v1
unifyLeft n1 v1 n2 v2 = do
  assert (tagEq v1 v2) $ "tag mismatch:\n" ++
           " nodes: " ++ sep n1 n2 ++ ";\n" ++
           " vals: " ++ sep v1 v2
  unifyMany (children v1) (children v2)

unifyMany :: [Name] -> [Name] -> VM ()
unifyMany n1 n2 = do
  assert (length n1 == length n2) ("unifyMany. length mismatch: " ++ sep n1 n2)
  sequence_ $ zipWith unify n1 n2

-- Needed when we unify two Vars together
substitute :: Name -> Name -> VM ()
substitute old new = do
  modifyAll subChildren
 where
  subName name | name == old = new
  subName x = x

  subChildren _ val =
    fmap subName val

-- Tree utilities
tagEq :: (Functor f, Eq (f ())) => f a -> f a -> Bool
tagEq t1 t2 = fmap (const ()) t1 == fmap (const ()) t2

children :: (T.Traversable t) => t a -> [a]
children t = fst $ T.mapAccumR step [] t
 where
  step list child = (child : list, ())

-- Stack Utilities --
stackName :: Stack -> Name
stackName (Stack s) = s

newVarStack :: VM Stack
newVarStack = do
  v <- var
  s <- store (Ptr v)
  return (Stack s)

newStack :: VM Stack
newStack = do
  nil <- store Nil
  s <- store (Ptr nil)
  return (Stack s)

push :: Stack -> Name -> VM ()
push (Stack stack) head = do
  Ptr tail <- get stack
  new <- store (Cons head tail)
  put stack (Ptr new)

pop :: Stack -> VM Name
pop (Stack stack) = do
  Ptr list <- get stack
  (p, head, tail) <- pair
  unify list p
  put stack (Ptr tail)
  return head

assertEmpty :: Stack -> VM ()
assertEmpty stack = do
  nil <- newStack
  unify (stackName stack) (stackName nil)

-- Stream processing
-- Top level parsing functions
parseWord :: Stack -> Dict -> Word -> VM ()
parseWord stack dict word = msum . map (handle) $ (mapMaybe ($ word) dict)
 where
  handle :: Rule -> VM ()
  handle rule = do
    s <- rule
    s' <- reduceLeft stack s
    pushSub stack s'

pushSub :: Stack -> Subl Name -> VM ()
-- Ambiguity
pushSub stack (Subl [] [] n) = pushTop `mplus` bindTop
  where
    pushTop = push stack n
    bindTop = do
      top <- pop stack
      Sub s <- get top
      s' <- bindRight n s
      pushSub stack s'
pushSub stack s@(Subl [] _ _) = do
  top <- store $ Sub s
  push stack top
-- pushSub has been misused; called on Subl term with preconditions remaining
pushSub _ s = assert False $ "pushSub. " ++ show s

-- Basic Parsers
type Word = String
type Parser = Word -> Maybe Rule
type Dict = [Parser]

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

tokenParser :: String -> Parser
tokenParser model = match model (tokenRule model)

matrixParse :: Parser
matrixParse = match "matrix" matrixRule

parenParse :: Parser
parenParse = match "(" parenRule

mainDictionary :: [Parser]
mainDictionary = [
  -- basic nodes
  intParse,
  matrixParse,
    tokenParser "by",

  -- match "*"
  imulParse,
  mmulParse,

  -- grouping
  parenParse,
    tokenParser ")"
 ]

-- Main Parser Functions --
-- Special handling of '(' , ')'
tokenize :: String -> [String]
tokenize = words . concatMap pad
 where
   pad '(' = " ( "
   pad ')' = " ) "
   pad x = [x]

-- Returns parse stack
parse :: String -> VM Stack
parse str =
  let stream = tokenize str in
  do stack <- newVarStack
     mapM_ (parseWord stack mainDictionary) stream
     return stack

-- Testing
main :: String -> IO ()
main = main' True
main' :: Bool -> String -> IO ()
main' closed str = chk $ do
  stack <- parse str
  -- get result
  val <- pop stack

  -- If closed is true, parsing will fail unless stack contains exactly one
  -- element
  if closed then 
    assertEmpty stack else
    return ()

  return val

chk :: VM Name -> IO ()
chk m =
  let worlds = runUM m
      (values, _) = unzip worlds
  in do
    mapM_
      (\(value, (_, env)) -> do
        putStrLn ">>>>>>>"
        mapM_ print (M.toList env)
        putStrLn "<<<<<<<"
        putStrLn ("VALUE: " ++ show value))
      worlds
    putStrLn ("-------\nPARSE COUNT: " ++ show (length values))


