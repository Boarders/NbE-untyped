{-# LANGUAGE Strict, LambdaCase, BlockArguments #-}

module Main where

import Data.Maybe (fromJust)
import qualified Data.Map as Map


main :: IO ()
main = print (nfTop True top example)

type Name = String

--------------------------------------
-- Just for printing readable terms --
--------------------------------------
data Named
  = LocN Name
  | TopN Name
  | AppN Named Named
  | LamN Name Term
  deriving Show

toNamed :: Term -> Named
toNamed = go 
  where go = undefined

  

data Term
  = Loc Int          -- de-bruijn index / name for printing purposes
  | Top Name         -- top-level name
  | App Term Term
  | Lam Name Term    -- Name for printing
  deriving Show

-- Neutral spines
data Spine
  = SNil             -- empty spine for top level definitions
  | SApp Spine ~Val  -- stuck application

-- Scott Domain + neutrals
data Val
  = VLam Name (Val -> Val)
  | VLoc Int  Spine         -- debruijn level   -- flattened neutrals
  | VTop Name Spine ~Val                        -- 

type TopEnv    = [(Name, Val)] -- for easy of implementation, Map would be more efficient
type LocEnv    = [Val]

-- To evaluate a local variable lookup in environment
-- We don't count for lookup failures as this is an invariant
-- of the DeBruijn representation
evalLocEnv :: Int -> LocEnv -> Val
evalLocEnv = flip (!!)

-- To evaluate a top-level variable, lookup in top level environment
evalTopEnv :: Name -> TopEnv -> Val
evalTopEnv n = fromJust . lookup n

eval :: TopEnv -> LocEnv -> Term -> Val
eval top loc = \case
  Loc i     -> evalLocEnv i loc
  Top n     -> evalTopEnv n top
  App t u   -> vapp (eval top loc t) (eval top loc u)
  Lam n t     -> VLam n \val -> eval top (val:loc) t  -- capture closure

-- Use metalanguage application or build up stuck term
vapp :: Val -> Val -> Val
vapp (VLam n body)      ~arg = body arg
vapp (VLoc level sp)    ~arg = VLoc level (SApp sp arg)
vapp (VTop name sp val) ~arg = VTop name (SApp sp arg) (vapp val arg)

-- Unfold definition or just spine
quoteSpine :: Int -> Bool -> Term -> Spine -> Term
quoteSpine depth unf h = \case
  SNil      -> h
  SApp sp u -> App (quoteSpine depth unf h sp) (quote depth unf u)

-- Readback term, keeping track of depth of binder for debruijn level
quote :: Int -> Bool -> Val -> Term
quote depth unf = \case
  VLoc i sp   ->
    quoteSpine depth unf (Loc ((depth - i) - 1)) sp -- convert from debruijn level to value
  VLam n body   ->
    let
      depth' = depth + 1       -- new debruijn level
      varVal = VLoc depth SNil
    in
      Lam n (quote depth' unf (body varVal))
  VTop x sp t -> if unf then quote depth unf t
                        else quoteSpine depth unf (Top x) sp

-- evaluate term with top level environment
evalTop :: [(Name, Term)] -> Term -> Val
evalTop top t = eval topvals [] t where
  topvals = foldl (\top (x, t) -> (x, eval top [] t) : top) [] top

-- normalise term with top level environment
nfTop :: Bool -> [(Name, Term)] -> Term -> Term
nfTop unf top t = quote 0 unf (evalTop top t)

------------------------------------------------------------

($$) = App
infixl 8 $$

top :: [(Name, Term)]
top =
  [ ("zero", Lam "s" $ Lam "z" $ Loc 0)
  , ("suc",
       let
         nsz = Loc 2 $$ Loc 1 $$ Loc 0
         s   = Loc 1
       in
         Lam "n" $ Lam "s"  $ Lam "z" $
         s $$ nsz)
  , ("add",
       let
         msz  = Loc 2 $$ Loc 1 $$ Loc 0
         n    = Loc 3
         s    = Loc 1
       in
         Lam "n" $ Lam "m" $ Lam "s" $ Lam "z" $
         n $$ s $$ msz)
  , ("5",
       Top "suc"
         $$ (Top "suc"
            $$ (Top "suc"
                $$ (Top "suc" $$
                     (Top "suc" $$
                        Top "zero")))))
  ]

example =
  let
    body = (Top "add" $$ Loc 0 $$ Loc 0)
    exp  = Lam "five" body
    arg  = Top "5"
  in
    exp $$ arg
