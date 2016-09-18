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
-- Note: all terms defined this way type check trivially, as there is only
--  one type, left implicit.
-- Note: this encoding admits open terms, but we will treat these an invalid
--  in what follows.

-- Ctx represents the terms bound by any lambda abstractions wrapping the
--  current term.  As we perform a beta reduction, the argument (Just arg) is
--  prepended to the Ctx for consistency with the use of DeBruijn indices.
-- Nothing is used as a placeholder to keep indices lined up when performing
--  recursive substitution.
type Ctx = [Maybe UTLCTerm]

-- lkup obtains from the Ctx the UTLCTerm by the DeBruijn index.  The
--  possibility that the DbIdx is free in the term is handled by wrapping the
--  result in the Maybe monad.
lkup :: Ctx -> DbIdx -> Maybe (Maybe UTLCTerm)
lkup []     _       = Nothing       -- The DbIdx is free.
lkup (a:as) O       = Just a        -- Found the term bound to DbIdx.
lkup (a:as) (S idx) = lkup as idx   -- Keep looking.

-- Perform substitutions from a fixed context.
-- In particular, do not perofrm beta reduction.
subst :: Ctx -> UTLCTerm -> Maybe UTLCTerm
subst ctx (Var idx)      = do val <- lkup ctx idx
                              Just $ case val of
                                Nothing -> Var idx
                                Just term -> term
subst ctx (Lam body)     = do body' <- subst (Nothing:ctx) body
                              return $ Lam body'
subst ctx (App term arg) = do term' <- subst ctx term
                              arg' <- subst ctx arg
                              return $ App term' arg'

-- Reduces a closed term to WHNF and an open term to Nothing.
whnfc :: Ctx -> UTLCTerm -> Maybe UTLCTerm
-- Finds the outermost redex and performs a single beta reduction.
whnfc ctx (App (Lam body) arg) = subst (Just arg:ctx) body
whnfc ctx (App term       arg) = do left <- whnfc ctx term
                                    subst ctx $ App left arg
-- Var and Lam are already in WHNF, so we just apply any substitutions.
whnfc ctx term                 = subst ctx term

-- WHNF wrapper that starts with an empty context.
whnf :: UTLCTerm -> Maybe UTLCTerm
whnf = whnfc []

-- Beta reduce as many times as possible.
eval :: UTLCTerm -> Maybe UTLCTerm
eval term = do term' <- whnf term
               if term == term'
               then return term
               else eval term'

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
    "i" ~: (whnf i) @?= Just i,
    "k" ~: (whnf k) @?= Just k,
    "s" ~: (whnf s) @?= Just s,
    "y" ~: (whnf y) @?= Just y],
  "i" ~: [
    "i i" ~: (whnf $ App i i) @?= Just i,
    "i k" ~: (whnf $ App i k) @?= Just k,
    "i s" ~: (whnf $ App i s) @?= Just s,
    "i y" ~: (whnf $ App i y) @?= Just y],
  "k" ~: [
    "k i" ~: (whnf $ App k i) @?= Just (Lam i),
    "k k" ~: (whnf $ App k k) @?= Just (Lam k),
    "k s" ~: (whnf $ App k s) @?= Just (Lam s),
    "k y" ~: (whnf $ App k y) @?= Just (Lam y),
    "k i i" ~: (whnf $ App (App k i) i) @?= Just (App (Lam i) i),
    "k i k" ~: (whnf $ App (App k i) k) @?= Just (App (Lam i) k),
    "k i s" ~: (whnf $ App (App k i) s) @?= Just (App (Lam i) s),
    "k i y" ~: (whnf $ App (App k i) y) @?= Just (App (Lam i) y)]]
eval_tests = "eval" ~: [
  "refl" ~: [
    "i" ~: (eval i) @?= Just i,
    "k" ~: (eval k) @?= Just k,
    "s" ~: (eval s) @?= Just s,
    "y" ~: (eval y) @?= Just y],
  "i" ~: [
    "i i" ~: (eval $ App i i) @?= Just i,
    "i k" ~: (eval $ App i k) @?= Just k,
    "i s" ~: (eval $ App i s) @?= Just s,
    "i y" ~: (eval $ App i y) @?= Just y],
  "k" ~: [
    "k i" ~: (eval $ App k i) @?= Just (Lam i),
    "k k" ~: (eval $ App k k) @?= Just (Lam k),
    "k s" ~: (eval $ App k s) @?= Just (Lam s),
    "k y" ~: (eval $ App k y) @?= Just (Lam y),
    "k i i" ~: (eval $ App (App k i) i) @?= Just i,
    "k i k" ~: (eval $ App (App k i) k) @?= Just i,
    "k i s" ~: (eval $ App (App k i) s) @?= Just i,
    "k i y" ~: (eval $ App (App k i) y) @?= Just i],
  "multi" ~: [
    "s k s k" ~: (eval $ App (App (App s k) s) k) @?= Just k]]
iota_tests = "iota" ~: [
  "i" ~: [
    "iota_i i" ~: (eval $ App iota_i i) @?= Just i,
    "iota_i k" ~: (eval $ App iota_i k) @?= Just k,
    "iota_i s" ~: (eval $ App iota_i s) @?= Just s,
    "iota_i y" ~: (eval $ App iota_i y) @?= Just y,
    "iota_i iota_i" ~: (eval $ App iota_i iota_i) @?= eval iota_i],
  "k" ~: [
    "iota_k i" ~: (eval $ App iota_k i) @?= Just (Lam i),
    "iota_k k" ~: (eval $ App iota_k k) @?= Just (Lam k),
    "iota_k s" ~: (eval $ App iota_k s) @?= Just (Lam s),
    "iota_k y" ~: (eval $ App iota_k y) @?= Just (Lam y),
    "iota_k i i" ~: (eval $ App (App iota_k i) i) @?= Just i,
    "iota_k i k" ~: (eval $ App (App iota_k i) k) @?= Just i,
    "iota_k i s" ~: (eval $ App (App iota_k i) s) @?= Just i,
    "iota_k i y" ~: (eval $ App (App iota_k i) y) @?= Just i]]
logic_tests = "logic" ~: [
  "neg" ~: [
    "tt" ~: (eval $ App neg tt) @?= Just ff,
    "ff" ~: (eval $ App neg ff) @?= Just tt],
  "doubleneg" ~: [
    "tt" ~: (eval $ App neg (App neg tt)) @?= Just tt,
    "ff" ~: (eval $ App neg (App neg ff)) @?= Just ff],
  "cond" ~: [
    "tt" ~: (eval $ App (App (App cond tt) tt) ff) @?= Just tt,
    "ff" ~: (eval $ App (App (App cond ff) tt) ff) @?= Just ff],
  "and" ~: [
    "tt tt" ~: (eval $ App (App and tt) tt) @?= Just tt,
    "tt ff" ~: (eval $ App (App and tt) ff) @?= Just ff,
    "ff tt" ~: (eval $ App (App and ff) tt) @?= Just ff,
    "ff ff" ~: (eval $ App (App and ff) ff) @?= Just ff],
  "or" ~: [
    "tt tt" ~: (eval $ App (App or tt) tt) @?= Just tt,
    "tt ff" ~: (eval $ App (App or tt) ff) @?= Just tt,
    "ff tt" ~: (eval $ App (App or ff) tt) @?= Just tt,
    "ff ff" ~: (eval $ App (App or ff) ff) @?= Just ff],
  "impl" ~: [
    "tt tt" ~: (eval $ App (App impl tt) tt) @?= Just tt,
    "tt ff" ~: (eval $ App (App impl tt) ff) @?= Just ff,
    "ff tt" ~: (eval $ App (App impl ff) tt) @?= Just tt,
    "ff ff" ~: (eval $ App (App impl ff) ff) @?= Just tt]]
tests = "algebraic untyped lambda calculus" ~: [whnf_tests, eval_tests, iota_tests, logic_tests]

main :: IO ()
main = do counts <- runTestTT tests
          return ()
