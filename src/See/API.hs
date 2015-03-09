module See.API where

import See.Types
import Monad.Condition

import qualified Data.Map as M

-- client:
--   text area
--   send update whenever complete new word is typed
--     can trigger simply on space?
-- 
-- server
--   incremental updates:
--     previous tokenstring diffed against new one
--     previous results (monad value) cached
--       Map [Token] (VM a, a)
--
--     e.g. when new token 'foo' received, extend previous VM with bind
--          and evaluate it
--
--     return (context-stack ref, assignments, environment)
--
-- rendering
--   haskell generates json tree?


-- base, new -> (prefix, new')
tdiff :: Eq a => [a] -> [a] -> ([a], [a])
tdiff base new =
  let prefix = map fst $ takeWhile (uncurry (==)) $ zip base new
  in (prefix, drop (length prefix) new)

type VEnv = WrittenEnv (Val Integer)
type Cache a = M.Map [Token] (VM a, [(Either Error a, VEnv)])

data Event = WordParse Token (Command Name) | Reduction (Command Name)

--readCache :: ([Token], [Token]) -> Cache (Val Integer) () -> 
readCache (prefix, new) cache =
  let full = prefix ++ new in
  case M.lookup full cache of
    Nothing ->
      case M.lookup prefix cache of
        Nothing -> makeVM full
        Just m -> (m >> makeVM new)
    Just m -> m

--makeVM :: [Token] -> VM (Context, [Event], VEnv)
makeVM = undefined
