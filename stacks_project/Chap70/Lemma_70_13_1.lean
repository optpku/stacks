/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap70.Lemma_70_13_3_AffineSpace

/-!
# Embedding an affine scheme into affine space over an algebraic space

A locally finite type morphism from an affine scheme into a quasi-separated,
locally separated algebraic space immerses into a finite-dimensional relative
affine space over the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.13.1: Let `S` be a scheme. Let `f : U ⟶ X` be a morphism of algebraic
spaces over `S`. Assume `U` is an affine scheme, `f` is locally of finite type,
and `X` is quasi-separated and locally separated in the absolute sense of
Definition 66.3.1. Then there exists an immersion
`U ⟶ AffineSpace (ULift (Fin n)) X` over `X`. -/
@[stacks 088L]
theorem exists_immersion_to_affineSpace {S : Scheme.{u}} {X U : AlgebraicSpace S}
    (f : U ⟶ X) [IsAffine U] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyLocallySeparated X] :
    ∃ (n : ℕ) (i : U ⟶ AffineSpace (ULift.{u} (Fin n)) X),
      IsImmersion i ∧ i ≫ AffineSpace.toBase (ULift.{u} (Fin n)) X = f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
