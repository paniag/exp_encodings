{-# LANGUAGE FlexibleInstances #-}

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

class UTLCTermTF t where
  -- Note that we're still using the algebraic DbIdx at this point.
  var :: DbIdx -> t
  lam :: t -> t
  app :: t -> t -> t

-- Ctx represents the terms bound by any lambda abstractions wrapping the
--  current term.  As we perform a beta reduction, the argument (Just arg) is
--  prepended to the Ctx for consistency with the use of DeBruijn indices.
-- Nothing is used as a placeholder to keep indices lined up when performing
--  recursive substitution in lambda abstractions.
type Ctx t = [Maybe t]

-- lkup obtains from the Ctx the UTLCTerm by the DeBruijn index.  The
--  possibility that the DbIdx is free in the term is handled by wrapping the
--  result in the Maybe monad.
lkup :: UTLCTermTF t => Ctx t -> DbIdx -> Maybe (Maybe t)
lkup []     _       = Nothing       -- The DbIdx is free. This information is
                                    --  is not used below, but there's nothing
                                    --  else sensible to return here.
lkup (a:as) O       = Just a        -- Found the term bound to DbIdx.
lkup (a:as) (S idx) = lkup as idx   -- Keep looking.

-- Define substitution on tagless final UTLC terms.
type Subst t = Ctx t -> t
instance UTLCTermTF t => UTLCTermTF (Subst t) where
  var idx ctx = let val = do val <- lkup ctx idx
                             return $ case val of
                               Nothing -> var idx
                               Just term -> term
                in case val of
                    Nothing -> var idx
                    Just val' -> val'
  lam body ctx = lam $ body ctx
  app term arg ctx = app (term ctx) (arg ctx)

-- WHNF on tagless final UTLC terms.
type WHNF t = Bool -> Ctx t -> t
instance UTLCTermTF t => UTLCTermTF (WHNF t) where
  var idx _ ctx = ((var :: DbIdx -> Subst t) idx) ctx
  lam body False ctx = (lam body :: Subst t) ctx
  lam body True ctx = (body :: Subst t) ctx
  app term arg _ ctx = (app (term True ctx) (arg False ctx) :: Subst t) ctx
