#!/usr/bin/env cabal
{- cabal:
build-depends: base, HaTeX
-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}

-- Welcome to Proofs.hs!
-- This is not used by the real proof... was just an experiment

import Data.String
import Control.Monad
import Text.LaTeX
import Text.LaTeX.Packages.AMSThm hiding (proof)
import qualified Text.LaTeX.Packages.AMSThm as AMSThm

type Latex = LaTeXM ()

main :: IO ()
main = renderFile "all_proofs.tex" (execLaTeXM all_proofs)

all_proofs :: Latex
all_proofs = do
  linear_subst
  linear_subst_alt

lemma :: Latex -> Latex
lemma = theorem "lemma"

proofCase :: Latex -> [Latex] -> Latex
proofCase titl steps = do
  item (Just "Case:")
  titl
  -- tabbing do
  --   forM_ (zip steps [1..]) \(step,i) -> do
  --     ("\"" <> show i <> "\"")
  --     math step

linear_subst :: Latex
linear_subst = do
  lemma "(Substitution of linear variables preserves typing)"
  AMSThm.proof Nothing do
    "By structural induction on the first derivation."
    description do
      proofCase "CaseWHNF" caseWHNF

linear_subst_alt :: Latex
linear_subst_alt = do
  lemma "(Substitution of linear variables in case alternatives preserves typing)"
  AMSThm.proof Nothing do
    "By structural induction on the alt judgment."
    description do
      proofCase "AltN" altZero

caseWHNF :: [Latex]
caseWHNF = []


altZero :: [Latex]
altZero =
  [ j g' bd' ld' e' s'
  , "Subcase x does not occur"
  , j 
  ]

