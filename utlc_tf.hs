-- {-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Test.HUnit

--
-- Algebraic types and conversions to make printing easier.
--

-- Variable bindings are inductively, algebraically defined DeBruijn indices.
data DbIdx = O
           | S DbIdx
  deriving (Eq, Show)

-- A term in the untyped lambda calculus is either...
data UTLCTermI = Var DbIdx                -- a DeBruijn index representation of
                                          --  a variable;
               | Lam UTLCTermI            -- a lambda abstracted term; or
               | App UTLCTermI UTLCTermI  -- an application of one term to another.
  deriving (Eq,Show)
-- Note: all terms defined this way type check trivially, as there is only
--  one type, left implicit.
-- Note: this encoding admits open terms, but we will treat these an invalid
--  in what follows.

--
-- Tagless Final Untyped Lambda Calculus
--

class UTLCTerm t where
  -- Note that we're still using the algebraic DbIdx at this point.
  var :: DbIdx -> t
  lam :: t -> t
  app :: t -> t -> t


newtype Subst t = Subst { subst :: Ctx t -> t }

instance UTLCTerm t => UTLCTerm (Subst t) where
  var idx          = Subst $ \ctx ->
                      let val = do val <- lkup ctx idx
                                   return $ case val of
                                    Nothing -> var idx
                                    Just term -> term
                      in case val of
                                  Nothing -> var idx
                                  Just val'' -> val''
  lam body = Subst $ \ctx -> lam $ subst body ctx
  app fun arg = Subst $ \ctx -> app (subst fun ctx) (subst arg ctx)

newtype WHNF t = WHNF { whnf :: Ctx t -> t }
newtype WHNFAppO t = WHNFAppO { whnfappo :: Ctx t -> t }
newtype WHNFAppI t = WHNFAppI { whnfappi :: Ctx t -> t }

instance UTLCTerm t => UTLCTerm (WHNF t) where
  var idx = WHNF $ \ctx -> subst (var idx) ctx
  lam body = WHNF $ \ctx -> subst (lam (Subst $ whnf body)) ctx
  app fun arg = WHNF $ \ctx -> case lamBody (whnf fun ctx) of
                                Nothing -> subst (app (Subst $ whnf fun ))

  whnfappo (app fun arg) ctx
                                        app (whnfappo fun (Just arg':ctx)) arg'
    where arg' = subst arg ctx

instance UTLCTerm t => UTLCTerm (WHNFAppO t) where
  var idx (_:ctx) = whnf (var idx) ctx
  lam body ctx = subst body ctx
  app fun arg (_:ctx) = whnf (app fun arg) ctx

newtype IsLam = IsLam { islam :: Bool }

instance UTLCTerm IsLam where
  var _ = IsLam False
  lam _ = IsLam True
  app _ _ = IsLam False


-- instance UTLCTerm (e -> t) where
--   var idx ev


-- class Evaltr f where
--   eval :: f -> f
--   eval = id

-- instance Evaltr (a -> b) where


-- type Eval t nx = t -> t -> nx
-- 
-- class UTLCTerm (e -> t) where
--   -- Note that we're still using the algebraic DbIdx at this point.
--   var :: DbIdx -> Eval (DbIdx -> t) -> t
--   var idx e = e var idx subst
--   -- e :: (DbIdx -> t) -> DbIdx -> t
--   lam :: t -> e -> t
--   lam body e = e lam body
--   -- e :: (t -> t) -> t -> t
--   app :: t -> t -> e -> t
--   app fun arg e = e app fun arg
--   -- e :: (t -> t -> t) -> t -> t -> t
--   --
--   -- e :: (a -> b) -> a -> b



-- Ctx represents the terms bound by any lambda abstractions wrapping the
--  current term.  As we perform a beta reduction, the argument (Just arg) is
--  prepended to the Ctx for consistency with the use of DeBruijn indices.
-- Nothing is used as a placeholder to keep indices lined up when performing
--  recursive substitution in lambda abstractions.
type Ctx t = [Maybe t]

-- lkup obtains from the Ctx the UTLCTerm by the DeBruijn index.  The
--  possibility that the DbIdx is free in the term is handled by wrapping the
--  result in the Maybe monad.
lkup :: Ctx t -> DbIdx -> Maybe (Maybe t)
lkup []     _       = Nothing       -- The DbIdx is free. This information is
                                    --  is not used below, but there's nothing
                                    --  else sensible to return here.
lkup (a:as) O       = Just a        -- Found the term bound to DbIdx.
lkup (a:as) (S idx) = lkup as idx   -- Keep looking.
