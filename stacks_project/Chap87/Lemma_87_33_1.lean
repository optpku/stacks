/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_33_1_Comparison

/-!
# Maps out of affine formal schemes, affine targets

For an affine scheme `X` over `S`, morphisms `Spec(A) ⟶ X` over `S` are in
bijection with morphisms `Spf(A) ⟶ X` over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- Lemma 87.33.1: Let `S` be a scheme. Let `A` be a weakly admissible
topological `S`-algebra. Let `X` be an affine scheme over `S`. Then the
natural map `Mor_S(Spec(A), X) ⟶ Mor_S(Spf(A), X)` is bijective. -/
@[stacks 0AQF]
theorem specHomToSpfHom_bijective {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}}
    (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    {X : Over S} [IsAffine X.left] :
    Function.Bijective (specHomToSpfHom structureHom X) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
