/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_58_1_ChernCap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Lemma 42.58.1

On a quasi-compact regular finite-type scheme over `S` with affine diagonal and
bounded relative dimension, Chern character followed by cap against `[X]` is an
isomorphism `K₀(Vect(X)) ⊗ ℚ ≃ CH_*(X) ⊗ ℚ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable (X : Over S) [LocallyOfFiniteType X.hom] [CompactSpace X.left]

/-- Lemma 42.58.1: In Situation 42.7.1, if `X` is a quasi-compact regular scheme of finite
type over `S` with affine diagonal and bounded relative dimension function `δ_{X/S}`, then
the composition of `chernCharacter` from Remark 42.56.5 with `c ↦ c ∩ [X]` is an
isomorphism `K₀(Vect(X)) ⊗ ℚ → CH_*(X) ⊗ ℚ`. -/
@[stacks 0FEY]
theorem toRationalChow_bijective
    [Scheme.Regular X.left] [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    (classes : ChernClass.Theory δ X.hom)
    (hδ : BddAbove (Set.range fun x : X.left ↦
      (X.hom.relativeDimensionFunction δ x).natAbs)) :
    Function.Bijective (toRationalChow_tensorQ δ X classes hδ) :=
  sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
