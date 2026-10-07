module

public import stacks_project.Chap91.Lemma_91_14_3_Extension
public import stacks_project.Chap91.Lemma_91_14_3_Pushout
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushout of square-zero f⁻¹𝒪_B-algebra extensions along a coefficient map

On a quasi-compact quasi-separated algebraic space, if DQ_X(ℱ) ⟶ DQ_X(𝒢) is an
isomorphism, then pushout along φ : ℱ ⟶ 𝒢 is an equivalence of categories of
identity-base square-zero f⁻¹𝒪_B-algebra extensions.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open SquareZeroAlgebraExtension

noncomputable section

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 91.14.3: if X is quasi-compact and quasi-separated and
DQ_X(ℱ) ⟶ DQ_X(𝒢) is an isomorphism, then the pushout functor F along
φ : ℱ ⟶ 𝒢 of identity-base square-zero f⁻¹𝒪_B-algebra extensions of 𝒪_X
is an equivalence of categories. Coefficients need not be quasi-coherent.
Here DQ_X is the right adjoint of DerivedQCoh.inclusion from Derived Categories
of Spaces 75.19. -/
@[stacks 0D3P]
instance pushout_isEquivalence (f : X ⟶ B)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) [IsIso (dqMap φ)] :
    Functor.IsEquivalence (pushoutFunctor f φ) :=
  sorry
