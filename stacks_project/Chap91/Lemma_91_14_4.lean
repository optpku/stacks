/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_14_4_Pushout
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushout of thickening solutions is an equivalence after DQ

On a quasi-compact quasi-separated algebraic space, if DQ_X(ℱ) ⟶ DQ_X(𝒢) is an
isomorphism, then pushout of solutions of 91.13.0.1 along φ : ℱ ⟶ 𝒢 is an
equivalence of categories.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open SquareZeroAlgebraExtension (dqMap)
open ThickeningSolution

noncomputable section

universe u

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- Lemma 91.14.4: if X is quasi-compact and quasi-separated and
DQ_X(ℱ) ⟶ DQ_X(𝒢) is an isomorphism, then the pushout functor FT along
φ : ℱ ⟶ 𝒢 of solutions of 91.13.0.1 for a first-order thickening i : B ⟶ B'
and a coefficient c : f⁻¹J ⟶ ℱ is an equivalence of categories. Coefficients
need not be quasi-coherent. Here DQ_X is the right adjoint of DerivedQCoh.inclusion
from Derived Categories of Spaces 75.19. -/
@[stacks 0D3Q]
instance ft_isEquivalence (i : B ⟶ B') [IsFirstOrderThickening i] (f : X ⟶ B)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) (c : Coeff i f ℱ) [IsIso (dqMap φ)] :
    Functor.IsEquivalence (pushoutFunctor i f φ c) :=
  sorry
