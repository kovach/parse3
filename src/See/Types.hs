{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module See.Types where

import qualified Data.Map as M
import Control.Monad
import Control.Monad.List
import Control.Monad.State hiding (get, put)
import qualified Control.Monad.State as S (get, put)
import Control.Applicative ((<$>), (<*>))
import Data.Maybe (fromJust, mapMaybe)
import qualified Data.Traversable as T (mapM, Traversable, sequence, mapAccumR)
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

-- Basic objects
var :: VM Name
var = store Var

property :: Name -> Tag -> VM Name
property name tag = do
  obj <- var
  store $ Prop (Link {tag = tag, root = name, object = obj})
  return obj

token :: Tag -> VM Name
token tag = store (Symbol tag)

pair :: VM (Name, Name, Name)
pair = do
 head <- var
 tail <- var
 p <- store (Cons head tail)
 return (p, head, tail)

-- Rules --
type Rule = VM (Subl Name)

integer :: Integer -> Rule
integer i = do
  v <- store (IntLit i)
  return $ Subl {pre = [], post = [], output = v}

matrix :: Rule
matrix = do
  m <- store (Val "matrix" [])
  r <- property m "rows"
  c <- property m "columns"
  by <- token "by"
  -- TODO parse `by` as a dimension object
  return $ Subl {pre = [c, by, r], post = [], output = m}

mmul :: Rule
mmul = do
  Subl [c1, _, r1] _ m1 <- matrix
  Subl [c2, _, r2] _ m2 <- matrix
  Subl [cp, _, rp] _ prod <- matrix

  unify c1 r2
  unify rp r1
  unify cp c2

  return $ Subl {pre = [m1], post = [m2], output = prod}

tokenRule :: Tag -> Rule
tokenRule tag = do
  t <- store (Symbol tag)
  return $ Subl {pre = [], post = [], output = t}

-- Rule Simplification
bindLeft :: Name -> Subl Name -> VM (Subl Name)
bindLeft name (Subl (x : xs) rs out) = do
  unify name x
  return $ Subl xs rs out

bindRight :: Name -> Subl Name -> VM (Subl Name)
bindRight name (Subl ls (x : xs) out) = do
  unify name x
  return $ Subl ls xs out

reduceLeft :: Stack -> Subl Name -> VM (Subl Name)
reduceLeft _ s@(Subl [] rs out) = return s
reduceLeft stack sub = do
  top <- pop stack
  sub' <- bindLeft top sub
  reduceLeft stack sub'

-- Debugging
sep s1 s2 = show s1 ++ ", " ++ show s2
printError :: String -> VM ()
printError msg = do
  env <- getEnv
  trace ("\n\nERROR\n\n" ++ msg ++ "\n\n" ++ unlines (map show env)) $ return ()

-- Unification
debugFlag = False
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
lookupWith f key [] = Nothing
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
unifyLeft n1 Var n2 v2 = do
  put n1 v2
unifyLeft n1 v1 n2 Var = unifyLeft n2 Var n1 v1
unifyLeft n1 v1 n2 v2 = do
  assert (tagEq v1 v2) $ "tag mismatch: " ++ sep v1 v2
  unifyMany (children v1) (children v2)

unifyMany :: [Name] -> [Name] -> VM ()
unifyMany n1 n2 = do
  assert (length n1 == length n2) ("unifyMany. length mismatch: " ++ sep n1 n2)
  sequence_ $ zipWith unify n1 n2

-- Tree utilities
tagEq :: (Functor f, Eq (f ())) => f a -> f a -> Bool
tagEq t1 t2 = fmap (const ()) t1 == fmap (const ()) t2

children :: (T.Traversable t) => t a -> [a]
children t = fst $ T.mapAccumR step [] t
 where
  step list child = (child : list, ())

-- Graph manipulation
properties :: Name -> VM [Link Name]
properties root = do
  refs isProp
 where
  isProp _ (Prop l@(Link {root = r, object = o})) | r == root = Just l
  isProp _ _ = Nothing

substitute :: Name -> Name -> VM ()
substitute old new = do
  modifyAll sub
 where
  fix name | name == old = new
  fix x = x
  sub _ val =
    fmap fix val

-- Stack stuff
stackName :: Stack -> Name
stackName (Stack s) = s

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

-- Stream processing
-- Top level parsing functions
step :: Stack -> Dict -> Word -> VM ()
step stack dict word = msum . map (handle) $ (mapMaybe ($ word) dict)
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

pushSub stack s@(Subl [] xs n) = do
  top <- store $ Sub s
  push stack top
pushSub stack s = assert False $ "pushSub. " ++ show s

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
  return (integer i)

mmulParse :: Parser
mmulParse = match "*" mmul

--imulParse :: Parser
--imulParse = match "*" imul

tokenParser :: String -> Parser
tokenParser model = match model (tokenRule model)

matrixParse :: Parser
matrixParse = match "matrix" matrix

mainDictionary = [intParse, mmulParse, tokenParser "by", matrixParse]

-- Testing
main :: Bool -> String -> IO ()
main closed str = chk $ do
  stack <- newStack
  let stream = words str
  mapM (step stack mainDictionary) stream

  -- If closed is true, parsing will fail unless stack contains exactly one element
  if closed
   then do
     stack2 <- newStack
     v <- var
     push stack2 v
     -- Single element
     unify (stackName stack) (stackName stack2)
   else return ()
  -- Return object
  pop stack

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


p0 = var >> var
p1 = do
 x <- token "x"
 y <- token "y"
 unify x y
 return ()
p2 = do
 x <- token "x"
 y <- token "x"
 z <- var
 unify x y
 unify y z
 return ()
p4 = do
  nil <- store Nil
  s <- store (Ptr nil)
  let stack = Stack s
  v1 <- var
  v2 <- var
  push stack v1
  push stack v2
  _ <- pop stack
  return ()

p5 = do
  s <- newStack
  mmul

-- returns 2 results (two ways to assoc), both 2 by 5
p6 = main True "2 by 3 matrix * 3 by 4 matrix * 4 by 5 matrix"
