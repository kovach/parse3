module Main where
import See.Types
import Name
import qualified Control.Monad.State as S
import Data.List (intercalate)

bar = foo

data Action = Binary | Prefix | Postfix | Node
 deriving (Show, Eq)

obj :: Action
obj = Node
binary :: Action
binary = Binary
postfix :: Action
postfix = Postfix
prefix :: Action
prefix = Prefix

basic :: [(String, Action)]
basic =
 [ ("∈", binary)
 , ("→", binary)
 , ("=", binary)
 , ("set", obj)
 , ("function", obj)

 , (",", binary)
 , ("and", binary)

 , ("a", prefix)
 , ("the", prefix)

 , ("let", prefix)
 , ("be", binary)

 , (".", postfix)

 , ("is", binary)
 ]

type Bindings = [(String, Name)]
-- TODO see Unification
type ParserState = (Bindings)

type M a = S.State Stacks a

type Tag = String
data Object = O Tag [Object]
 deriving (Eq)
instance Show Object where
  show (O tag args) =
    wrap $
      tag ++ pnext (intercalate "," (map show args))
pnext "" = ""
pnext str = " " ++ str
wrap s = "(" ++ s ++ ")"
data Need = Pre | Post
 deriving (Show, Eq)
data Subl = Subl Tag [Post] [Need]
 deriving (Show, Eq)
type Pre = [Subl]
type Post = [Object]
type Stacks = (Post, Pre)
emptyContext = ([], [])
type Symbol = Tag
step :: Symbol -> M ()
step sym = 
  case lookup sym basic of
    Nothing -> pushObject (O sym [])
    Just tp ->
      case tp of
--        Binary -> _
        Prefix -> do
          pushSub (Subl sym [] [Post])
        Postfix -> do
          o <- pop
          pushObject (O sym [o])
        Node -> pushObject (O sym [])
update :: M Bool
update = do
  withTopSub handleFirstNeed

withTopSub fn = do
  (pre, post) <- get
  case post of
    [] -> return False
    (x : xs) -> do
      new <- fn x
      case new of
        Just x' -> put (pre, x' : xs)
        Nothing -> put (pre, xs)
      return True

handleFirstNeed :: Subl -> M (Either Object Subl)
handleFirstNeed (Subl tag objs []) = Left (Obj tag objs)
handleFirstNeed (Subl tag objs (x : xs)) = do
  o <- pop
  return $ Right (Subl tag (o : objs) xs)

pushObject :: Object -> M ()
pushObject o = S.modify (\(pre, post) -> (o : pre, post))
pop :: M Object
pop = do
  (x : xs, post) <- S.get
  S.put (xs, post)
  return x


s1 = ["set", ".", "."]

chk m = mapM_ print $ fst $ S.execState (mapM step m) emptyContext


{-
 - symbol
 - if postf ∈ symbol
 -   take top obj
 - if pref ∈ symbol
 -   push subl onto pre stack
 - -}
