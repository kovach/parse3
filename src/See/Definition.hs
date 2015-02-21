module See.Definition where
import See.Types


-- Takes a subgraph and recreates it.
-- Should be equivalent to rerunning the VM action that added it.
--
-- Subgraph is a contiguous block of names
-- should be 'self contained'
--
--
-- def -> new stack, add Frame object (or just a pointer to current
--          log entry)
-- symbol -> add SVar to ctxt, so it shadows any previous def
-- :
-- ... stuff
-- is _ -> rhs object, with property pointing at _
-- where clause -> (recursive is)
-- ∎ -> we have a stack with some stuff (lhs)
--   and an is-generated rhs object, so do the subl unify
--   and add symbol to to global context, with pointer to
--   rhs and a subgraph delimited by Frame
-- 
-- def rule will return special value (not Subl)
-- outer parser will dispatch on Subl/DefResolve
--
-- 2/18: OR
--  replace subl pre/post [] with internal lists
--   on stack pushes, ambiguously resolve pre/post demands
--

reinterpret :: Name -> VM ()
reinterpret = undefined
