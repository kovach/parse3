-- TODO
--  !!
--  use context to resolve words
--  implement ∎
--  !!
--
--  print output graph
--    and especially: the context stack
--
--  split up this file
--  use Condition monad
--  web client
--  better factoring for rule vs parser split?
--  make Ptrs immutable? need to add an 'Update' Val, cache object?
--  better syntax for specifing unification patterns
--    see: isNil, isCons
--
module See.Parse where
import See.Types
import See.Definition

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

-- Basic objects, Property Utilities --
var :: VM Name
var = store Var

property :: Name -> Tag -> VM Name
property name tag = do
  obj <- var
  _ <- store $ Prop (Link {tag = tag, root = name, object = obj})
  return obj

propertyVal root tag obj = do
  _ <- store $ Prop (Link {tag = tag, root = root, object = obj})
  return ()

setProperty :: Name -> Tag -> Name -> VM ()
setProperty name tag val = do
  p <- getProperty name tag
  unify p val

isVal :: Name -> VM ()
isVal name = do
  v <- get name
  case v of
    Val _ -> return ()
    Var -> return ()
    Ref _ -> return ()
    Symbol _ -> return ()
    IntLit _ -> return ()
    _ -> mzero

isNil :: Name -> VM ()
isNil n = do
  nil <- store Nil
  unify n nil

isCons:: Name -> VM (Name, Name)
isCons n = do
 head <- var
 tail <- var
 pattern <- store (Cons head tail)
 unify n pattern
 return (head, tail)

isBinding :: Tag -> Name -> VM Name
isBinding tag n = do
  value <- var
  binding <- store (Binding tag value)
  unify n binding
  return value

storeList :: [Name] -> VM Name
storeList [] = store Nil
storeList (x : xs) = do
  tail <- storeList xs
  store $ Cons x tail

sublVar :: VM Name
sublVar = do
  pre <- var
  post <- var
  out <- var
  store $ Sub (Subl {pre = pre, post = post, output = Push out})

-- Elementary Objects, Rules --
type Rule = VM (Subl Name)

-- Current pattern:
--  an object type is a VM action that returns a tuple of Names
--    first -> Val representing object
--    each other -> a property
--  this makes it easy to immediately impose relations on properties
--  see mmulRule below for example

integer :: VM (Name, Name)
integer = do
  i <- store (Val "integer")
  val <- property i "value"
  return (i, val)

-- TODO add integer constraint
matrix :: VM (Name, Name, Name)
matrix = do
  m <- store (Val "matrix")
  (rows, _) <- integer
  (columns, _) <- integer
  propertyVal m "rows" rows
  propertyVal m "columns" columns
  return (m, rows, columns)

symbol :: VM (Name, Name)
symbol = do
  s <- store (Val "symbol")
  val <- property s "value"
  return (s, val)

symbolLit :: Tag -> VM Name
symbolLit tag = store (Symbol tag)

integerRule :: Integer -> Rule
integerRule i = do
  (obj, val) <- integer
  lit <- store $ IntLit i
  unify val lit
  nil <- store Nil
  return $ Subl {pre = nil, post = nil, output = Push obj}

symbolRule :: Tag -> Rule
symbolRule tag = do
  (obj, val) <- symbol
  lit <- symbolLit tag
  unify val lit
  nil <- store Nil
  return $ Subl {pre = nil, post = nil, output = Push obj}

tokenRule :: Tag -> Rule
tokenRule tag = do
  lit <- symbolLit tag
  nil <- store Nil
  return $ Subl {pre = nil, post = nil, output = Push lit}

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

--tokenRule :: Tag -> Rule
--tokenRule tag = do
--  (s, val) <- symbol
--  t <- symbolLit tag
--  unify val t
--  nil <- store Nil
--  return $ Subl {pre = nil, post = nil, output = Push s}

-- TODO make this right-biased; should reduce unnecessary ambiguity
parenRule :: Rule
parenRule = do
  body <- var
  right <- symbolLit ")"
  nil <- store Nil
  post <- storeList [body, right]
  return $ Subl {pre = nil, post = post, output = Push body}

-- def _sym_ : -> push context, push empty stack
-- ∎ -> pop context, pop stack, resolve _sym_, insert into context
-- need to add new case to Subl type, or wrap it
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

-- syntactic pop
popRule :: Rule
popRule = do
  nil <- store Nil
  getlost <- var
  pre <- storeList [getlost]
  return $ Subl {pre = pre, post = nil, output = DoNothing}

-- Rule Simplification
-- TODO remove dead code, or use it to optimize?
bindLeft :: Name -> Subl Name -> VM (Subl Name)
bindLeft name (Subl pre post out) = 
 --trace ("LOOK: " ++ sep name pre) $ do
 do
  (head, tail) <- isCons pre
  isVal name
  unify name head
  return $ Subl tail post out
--bindLeft name (Subl (x : xs) rs out) = do
--  unify name x
--  return $ Subl xs rs out
--bindLeft a b = error $ "bindLeft. " ++ sep a b

bindRight :: Name -> Subl Name -> VM (Subl Name)
bindRight name (Subl pre post out) = do
  (head, tail) <- isCons post
  isVal name
  unify name head
  return $ Subl pre tail out
--bindRight name (Subl ls (x : xs) out) = do
--  unify name x
--  return $ Subl ls xs out
--bindRight a b = error $ "bindRight. " ++ sep a b

-- TODO may diverge when stack is a Var
reduceLeft :: Stack -> Subl Name -> VM (Subl Name)
reduceLeft stack s@(Subl pre _ _) = matchNil `mplus` matchCons
 where
   matchNil = do
     isNil pre
     return s
   matchCons = do
     top <- pop stack
     s' <- bindLeft top s
     reduceLeft stack s'
--reduceLeft stack s@(Subl pre _ _) = do
--  pval <- get pre
--  case pval of
--    Nil -> return s
--    _ -> do
--      top <- pop stack
--      s' <- bindLeft top s
--      reduceLeft stack s'
--reduceLeft _ s@(Subl [] _ _) = return s
--reduceLeft stack sub = do
--  top <- pop stack
--  sub' <- bindLeft top sub
--  reduceLeft stack sub'

-- Debugging
debugFlag :: Bool
debugFlag = False

sep :: (Show a, Show b) => a -> b -> String
sep s1 s2 = show s1 ++ ", " ++ show s2

simplePrintError :: String -> VM ()
simplePrintError msg = trace ("ERROR:\n" ++ msg ++ "\n") (return ())

printError :: String -> VM ()
printError msg = do
  env <- getEnv
  trace ("\n\nERROR\n\n" ++ msg ++ "\n\n" ++ unlines (map show env)) $ return ()

-- Unification
assert :: Bool -> String -> VM ()
assert cond msg = if cond then return () else do
  -- This is noisy since it prints for every failed branch
  if debugFlag
    then simplePrintError msg
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
  mapM_ (unifyProperty left) rightProps
  mapM_ (unifyProperty right) leftProps

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
-- Should this happen? (it has)
unifyLeft n1 _ n2 _ | n1 == n2 = return ()
-- TODO cleaner way to do this?
unifyLeft n1 Var n2 Var = do
  substitute n1 n2
  put n1 (Ref n2)
unifyLeft n1 Var _ v2 =
  case v2 of
    Ref n | n == n1 -> return ()
    _ -> put n1 v2
unifyLeft _ (Ref n1') n2 _ =
  unify n1' n2
unifyLeft n1 _ _ (Ref n2') =
  unify n1 n2'
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
-- Doesn't have to be recursive
substitute :: Name -> Name -> VM ()
substitute old new = do
  modifyAll subChildren
 where
  subName name | name == old = new
  subName x = x

  subChildren _ val =
    fmap subName val

-- Stack Utilities --
stackName :: Stack -> Name
stackName (Stack s) = s

-- Creates empty stack
newStack :: VM Stack
newStack = do
  nil <- store Nil
  s <- store (Ptr nil)
  return (Stack s)

-- Creates variable stack
newVarStack :: VM Stack
newVarStack = do
  v <- var
  s <- store (Ptr v)
  return (Stack s)

push :: Stack -> Name -> VM ()
push (Stack stack) head = do
  Ptr tail <- get stack
  new <- store (Cons head tail)
  put stack (Ptr new)

pop :: Stack -> VM Name
pop (Stack stack) = do
  Ptr list <- get stack
  (head, tail) <- isCons list
  put stack (Ptr tail)
  return head

top :: Stack -> VM Name
top (Stack stack) = do
  Ptr list <- get stack
  (head, _) <- isCons list
  return head

topStack :: Context -> VM Stack
topStack (Context s) = do
  Frame _ s _ <- get =<< top s
  return (Stack s)

topEnv :: Context -> VM Stack
topEnv (Context s) = do
  Frame _ _ e <- get =<< top s
  return (Stack e)

isEmpty :: Stack -> VM ()
isEmpty (Stack stack) = do
  Ptr s <- get stack
  isNil s

-- Context Management --
-- The context lookup table is kept as a stack
newFrame :: Maybe Tag -> Context -> VM (Stack, Stack)
newFrame mtag (Context s) = do
  Stack stack <- newStack
  Stack env <- newStack
  frame <- store (Frame mtag stack env)
  push s frame
  return (Stack stack, Stack env)

initialContext :: VM Context
initialContext = do
  s <- newVarStack
  let c = Context s
  _ <- newFrame Nothing c
  return c


pushBinding :: Stack -> Tag -> Name -> VM ()
pushBinding stack tag name = do
  store (Binding tag name) >>= push stack

newBinding :: Context -> Tag -> Name -> VM ()
newBinding context tag name = do
  e <- topEnv context
  pushBinding e tag name

-- TODO
-- currently this keeps looking after a match is found,
-- which may be desirable to maximize ambiguity 
--
-- we could change it to 
--   matchHead `mplus` (not matchHead >> matchTail)
--   or do an explicit match on the tag of the first element
lookupBinding :: Stack -> Tag -> VM Name
lookupBinding (Stack s) tag = do
  Ptr n <- get s
  lookupBinding' n tag

lookupBinding' :: Name -> Tag -> VM Name
lookupBinding' context tag = matchHead `mplus` matchTail
 where
   -- This handles the case that context is a Var
   matchHead = do
     (head, _) <- isCons context

     value <- isBinding tag head
     return value

   -- Don't use unify to avoid unbounded recursion when context is a Var
   matchTail = do
     -- TODO use case to avoid 'fail'? -- although,
     --   might be nice to avoid cluttering tree with end-of-context Lefts
     Cons _ tail <- get context
     lookupBinding' tail tag

parseBinding :: Stack -> Tag -> VM (Subl Name)
parseBinding env tag = do
  Sub s <- get =<< lookupBinding env tag
  trace ("LOOK: " ++ show s) $ return s

-- Top level parsing functions
parseWord :: Context -> Dict -> Word -> VM ()
parseWord context dict word = do
  stack <- topStack context
  env   <- topEnv context
  let step r = reduceSubl stack r >>= unfoldCommand context
  let rules = case mapMaybe ($ word) dict of
                [] -> [parseBinding env word, symbolRule word]
                rs -> rs
  -- Run each rule, reduce the Subl, combine
  msum . map (step =<<) $ rules

unfoldCommand :: Context -> Maybe (Command Name) -> VM ()
unfoldCommand _ Nothing = return ()
unfoldCommand context (Just command) = do
  stack <- topStack context
  mc <- case command of
          DoNothing -> return Nothing
          DoSub s -> reduceSubl stack s
          Push s ->
            (push stack s >> return Nothing)
              `mplus`
            (Just . DoSub <$> bindTop stack s)
          CreateFrame sym -> do
            Symbol tag <- get sym
            _ <- newFrame (Just tag) context
            v <- sublVar
            newBinding context tag v
            return Nothing
          CloseFrame -> trace "CLOSING" $ do
            let Context stack = context
            -- Resolve stack, pull mtag out of env, bind it
            Frame mtag stack env <- get =<< pop stack
            -- TODO resolve stack
            case mtag of
              Nothing -> return Nothing
              -- Insert binding into higher environment
              Just tag -> do
                -- TODO this right?
                isEmpty (Stack stack)
                -- TODO clean this up
                val <- lookupBinding (Stack env) tag
                packed <- packBlock val
                newBinding context tag packed
                return (Just (Push packed))

  unfoldCommand context mc

-- Reduces Subl using stack, 
reduceSubl :: Stack -> Subl Name -> VM (Maybe (Command Name))
reduceSubl stack s = do
  s'@(Subl pre _ _) <- reduceLeft stack s
  isNil pre
  incomplete s' `mplus` complete s'
 where
   complete (Subl _ post out) = do
     isNil post
     return $ Just out
   incomplete s@(Subl _ post out) = do
     (_, _) <- isCons post
     sub <- store (Sub s)
     push stack sub
     return Nothing


bindTop :: Stack -> Name -> VM (Subl Name)
bindTop stack n = do
  Sub s <- get =<< pop stack
  bindRight n s


-- Basic Parsers --
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
  definitionParse

 ]

-- Main Parser Functions --
-- Special handling of '(' , ')'
tokenize :: String -> [String]
tokenize = words . concatMap pad
 where
   pad '(' = " ( "
   pad ')' = " ) "
   pad ':' = " : "
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

