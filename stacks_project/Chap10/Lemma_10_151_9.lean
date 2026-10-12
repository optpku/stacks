/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.MvPolynomialCriterion
import StacksCheckRecall

/-!
# Étale polynomial presentations

@stack 0G1C

The coordinate-differential and local-dimension machinery, together with the
source-facing criterion, is owned by the ReasLib etale leaf.
-/

@[expose] public section

@[stacks 0G1C "polynomial etale criterion"]
#check @Algebra.Etale.mvPolynomial_iff_localDimension_and_differentials
