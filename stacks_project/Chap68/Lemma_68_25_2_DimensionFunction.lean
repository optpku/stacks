/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg

/-!
# Relative dimension functions on algebraic spaces

The integer-valued function on `|X|` obtained by adding residue-field
transcendence degree of the structure morphism to a dimension function on the
base scheme.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative dimension function associated to an algebraic space `X` over `S`
and `δ : S → ℤ` sends a point `x` to `δ (Points.base x)` plus the residue-field
transcendence degree of `x` over its image in `S`. -/
noncomputable abbrev relativeDimensionFunction {S : Scheme.{u}}
    (X : AlgebraicSpace S) (δ : S → ℤ) : Points X → ℤ :=
  fun x ↦ δ (Points.base x) + (residueFieldTrdegAt (toBase X) x : ℤ)

/-- `relativeDimensionFunction X δ` evaluates to `δ` at the image in `S` plus the
residue-field transcendence degree of the structure morphism. -/
theorem relativeDimensionFunction_apply {S : Scheme.{u}} (X : AlgebraicSpace S)
    (δ : S → ℤ) (x : Points X) :
    relativeDimensionFunction X δ x =
      δ (Points.base x) + (residueFieldTrdegAt (toBase X) x : ℤ) :=
  sorry

/-- Along an étale morphism `φ : ofOver U ⟶ X` from a scheme, the relative
dimension function on `X` pulls back to the scheme-level relative dimension
function of `U.hom`. -/
theorem relativeDimensionFunction_mapOfOver {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (δ : S → ℤ) (u : U.left) :
    relativeDimensionFunction X δ (Points.mapOfOver φ u) =
      U.hom.relativeDimensionFunction δ u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
