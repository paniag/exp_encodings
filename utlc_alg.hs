module Main where

import Prelude hiding (or, and)
import Test.HUnit

-- Variable bindings are inductively, algebraically defined DeBruijn indices.
data DbIdx = O
           | S DbIdx
  deriving (Eq, Show)

-- A term in the untyped lambda calculus is either...
data UTLCTerm = Var DbIdx               -- a DeBruijn index representation of
                                        --  a variable;
              | Lam UTLCTerm            -- a lambda abstracted term; or
              | App UTLCTerm UTLCTerm   -- an application of one term to another.
  deriving (Eq,Show)
-- Note: all terms defined this way type check trivially, as there is implicitly
--  only one type.
-- Note: this encoding admits open terms, which may or may not be a good idea,
--  but allows slight simplification of the code below.

-- Ctx represents the terms bound by any lambda abstractions wrapping the
--  current term.  As we perform a beta reduction, the argument (Just arg) is
--  prepended to the Ctx for consistency with the use of DeBruijn indices.
-- Nothing is used as a placeholder to keep indices lined up when performing
--  recursive substitution in lambda abstractions.
type Ctx = [Maybe UTLCTerm]

-- lkup obtains from the Ctx the UTLCTerm by the DeBruijn index.  The
--  possibility that the DbIdx is free in the term is handled by wrapping the
--  result in the Maybe monad.
lkup :: Ctx -> DbIdx -> Maybe (Maybe UTLCTerm)
lkup []     _       = Nothing       -- The DbIdx is free. This information is
                                    --  is not used below, but there's nothing
                                    --  else sensible to return here.
lkup (a:as) O       = Just a        -- Found the term bound to DbIdx.
lkup (a:as) (S idx) = lkup as idx   -- Keep looking.

-- Perform substitutions from a fixed context.
-- In particular, do not perform beta reduction.
subst :: Ctx -> UTLCTerm -> UTLCTerm
-- The Var case became more complicated in exchange for dropping the Maybe
-- monad wrapping the return value of these evaluation functions.
subst ctx (Var idx)      = let val = do val <- lkup ctx idx
                                        return $ case val of
                                          Nothing -> Var idx
                                          Just term -> term
                           in case val of
                            Nothing -> Var idx
                            Just val' -> val'
subst ctx (Lam body)     = Lam $ subst (Nothing:ctx) body
subst ctx (App term arg) = App (subst ctx term) (subst ctx arg)

-- Reduces a term to WHNF.
whnfc :: Ctx -> UTLCTerm -> UTLCTerm
-- Finds the outermost redex and performs a single beta reduction.
whnfc ctx (App (Lam body) arg) = subst (Just arg:ctx) body
whnfc ctx (App term       arg) = subst ctx $ App (whnfc ctx term) arg
-- Var and Lam are already in WHNF, so we just apply any substitutions.
whnfc ctx term                 = subst ctx term

-- WHNF wrapper that starts with an empty context.
whnf :: UTLCTerm -> UTLCTerm
whnf = whnfc []

-- Beta reduce as many times as possible.
eval :: UTLCTerm -> UTLCTerm
eval term = if term == term' then term else eval term'
  where term' = whnf term

-- SKI combinator calculus
i :: UTLCTerm
i = Lam $ Var O

k :: UTLCTerm
k = Lam $ Lam $ Var (S O)

s :: UTLCTerm
s = Lam $ Lam $ Lam $ App (App (Var $ S $ S O) (Var O)) (App (Var $ S O) (Var O))

-- Iota combinator calculus
iota :: UTLCTerm
iota = Lam $ App (App (Var O) s) k

-- SKI combinator calculus reimplemented in Iota combinator calculus.
iota_i :: UTLCTerm
iota_i = App iota iota

iota_k :: UTLCTerm
iota_k = App iota (App iota iota_i)

iota_s :: UTLCTerm
iota_s = App iota iota_k

-- The Y combinator.
y :: UTLCTerm
y = Lam $ App (Lam $ App (Var $ S O) (App (Var O) (Var O))) (Lam $ App (Var $ S O) (App (Var O) (Var O)))

-- Boolean Logic
tt :: UTLCTerm
tt = Lam $ Lam $ Var $ S O

ff :: UTLCTerm
ff = Lam $ Lam $ Var O

cond :: UTLCTerm
cond = Lam $ Lam $ Lam $
        App (App (Var $ S $ S O)
                 (Var $ S O))
            (Var O)
ifv :: DbIdx -> UTLCTerm -> UTLCTerm -> UTLCTerm
ifv idx thenv elsev = App (App (App cond (Var idx)) thenv) elsev

neg :: UTLCTerm
neg = Lam $ ifv O ff tt

and :: UTLCTerm
and = Lam $ Lam $ ifv (S O) (ifv O tt ff) ff

or :: UTLCTerm
or = Lam $ Lam $ ifv (S O) tt (ifv O tt ff)

impl :: UTLCTerm
impl = Lam $ Lam $ App (App or (App neg (Var (S O)))) (Var O)

-- Tests
whnf_tests = "whnf" ~: [
  "refl" ~: [
    "i" ~: (whnf i) @?= i,
    "k" ~: (whnf k) @?= k,
    "s" ~: (whnf s) @?= s,
    "y" ~: (whnf y) @?= y],
  "i" ~: [
    "i i" ~: (whnf $ App i i) @?= i,
    "i k" ~: (whnf $ App i k) @?= k,
    "i s" ~: (whnf $ App i s) @?= s,
    "i y" ~: (whnf $ App i y) @?= y],
  "k" ~: [
    "k i" ~: (whnf $ App k i) @?= Lam i,
    "k k" ~: (whnf $ App k k) @?= Lam k,
    "k s" ~: (whnf $ App k s) @?= Lam s,
    "k y" ~: (whnf $ App k y) @?= Lam y,
    "k i i" ~: (whnf $ App (App k i) i) @?= App (Lam i) i,
    "k i k" ~: (whnf $ App (App k i) k) @?= App (Lam i) k,
    "k i s" ~: (whnf $ App (App k i) s) @?= App (Lam i) s,
    "k i y" ~: (whnf $ App (App k i) y) @?= App (Lam i) y]]
eval_tests = "eval" ~: [
  "refl" ~: [
    "i" ~: (eval i) @?= i,
    "k" ~: (eval k) @?= k,
    "s" ~: (eval s) @?= s,
    "y" ~: (eval y) @?= y],
  "i" ~: [
    "i i" ~: (eval $ App i i) @?= i,
    "i k" ~: (eval $ App i k) @?= k,
    "i s" ~: (eval $ App i s) @?= s,
    "i y" ~: (eval $ App i y) @?= y],
  "k" ~: [
    "k i" ~: (eval $ App k i) @?= (Lam i),
    "k k" ~: (eval $ App k k) @?= (Lam k),
    "k s" ~: (eval $ App k s) @?= (Lam s),
    "k y" ~: (eval $ App k y) @?= (Lam y),
    "k i i" ~: (eval $ App (App k i) i) @?= i,
    "k i k" ~: (eval $ App (App k i) k) @?= i,
    "k i s" ~: (eval $ App (App k i) s) @?= i,
    "k i y" ~: (eval $ App (App k i) y) @?= i],
  "multi" ~: [
    "s k s k" ~: (eval $ App (App (App s k) s) k) @?= k]]
iota_tests = "iota" ~: [
  "i" ~: [
    "iota_i i" ~: (eval $ App iota_i i) @?= i,
    "iota_i k" ~: (eval $ App iota_i k) @?= k,
    "iota_i s" ~: (eval $ App iota_i s) @?= s,
    "iota_i y" ~: (eval $ App iota_i y) @?= y,
    "iota_i iota_i" ~: (eval $ App iota_i iota_i) @?= eval iota_i],
  "k" ~: [
    "iota_k i" ~: (eval $ App iota_k i) @?= Lam i,
    "iota_k k" ~: (eval $ App iota_k k) @?= Lam k,
    "iota_k s" ~: (eval $ App iota_k s) @?= Lam s,
    "iota_k y" ~: (eval $ App iota_k y) @?= Lam y,
    "iota_k i i" ~: (eval $ App (App iota_k i) i) @?= i,
    "iota_k i k" ~: (eval $ App (App iota_k i) k) @?= i,
    "iota_k i s" ~: (eval $ App (App iota_k i) s) @?= i,
    "iota_k i y" ~: (eval $ App (App iota_k i) y) @?= i]]
logic_tests = "logic" ~: [
  "neg" ~: [
    "tt" ~: (eval $ App neg tt) @?= ff,
    "ff" ~: (eval $ App neg ff) @?= tt],
  "doubleneg" ~: [
    "tt" ~: (eval $ App neg (App neg tt)) @?= tt,
    "ff" ~: (eval $ App neg (App neg ff)) @?= ff],
  "cond" ~: [
    "tt" ~: (eval $ App (App (App cond tt) tt) ff) @?= tt,
    "ff" ~: (eval $ App (App (App cond ff) tt) ff) @?= ff],
  "and" ~: [
    "tt tt" ~: (eval $ App (App and tt) tt) @?= tt,
    "tt ff" ~: (eval $ App (App and tt) ff) @?= ff,
    "ff tt" ~: (eval $ App (App and ff) tt) @?= ff,
    "ff ff" ~: (eval $ App (App and ff) ff) @?= ff],
  "or" ~: [
    "tt tt" ~: (eval $ App (App or tt) tt) @?= tt,
    "tt ff" ~: (eval $ App (App or tt) ff) @?= tt,
    "ff tt" ~: (eval $ App (App or ff) tt) @?= tt,
    "ff ff" ~: (eval $ App (App or ff) ff) @?= ff],
  "impl" ~: [
    "tt tt" ~: (eval $ App (App impl tt) tt) @?= tt,
    "tt ff" ~: (eval $ App (App impl tt) ff) @?= ff,
    "ff tt" ~: (eval $ App (App impl ff) tt) @?= tt,
    "ff ff" ~: (eval $ App (App impl ff) ff) @?= tt]]
tests = "algebraic untyped lambda calculus" ~: [whnf_tests, eval_tests, iota_tests, logic_tests]

main :: IO ()
main = do counts <- runTestTT tests
          return ()
