/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.SetTheory.Cardinal.Basic
public import stacks_project.Chap03.Lemma_3_9_4_Size
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# The cardinal λ of schemes and algebraic spaces

`lambda T` is the smallest infinite cardinal bounding the cardinalities of the
residue fields of a scheme `T`. For an algebraic space, `lambda X` is `lambda`
of any scheme presenting `X` by a surjective étale morphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

namespace AlgebraicGeometry.Scheme

/-- The smallest infinite cardinal bounding the cardinalities of residue fields of
a scheme. -/
noncomputable def lambda (T : Scheme.{u}) : Cardinal.{u} :=
  ℵ₀ ⊔ ⨆ t : T, #(T.residueField t)

/-- `lambda T` is the supremum of `ℵ₀` and the cardinalities of the residue fields
of `T`. -/
theorem lambda_def (T : Scheme.{u}) :
    lambda T = ℵ₀ ⊔ ⨆ t : T, #(T.residueField t) :=
  sorry

/-- Countable infinite cardinals are bounded by `lambda T`. -/
theorem aleph0_le_lambda (T : Scheme.{u}) : ℵ₀ ≤ lambda T := sorry

/-- The cardinality of a residue field is bounded by `lambda T`. -/
theorem cardinalMk_residueField_le_lambda (T : Scheme.{u}) (t : T) :
    #(T.residueField t) ≤ lambda T :=
  sorry

/-- `lambda T` is bounded by the Stacks size of `T`. -/
theorem lambda_le_size (T : Scheme.{u}) : lambda T ≤ T.size := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.AlgebraicSpace

/-- The cardinal `lambda X` of an algebraic space, as `lambda` of a chosen scheme
presenting `X` by a representable étale locally-surjective atlas. -/
noncomputable def lambda {S : Scheme.{u}} (X : AlgebraicSpace S) : Cardinal.{u} :=
  Scheme.lambda (Classical.choose X.atlas).left

/-- `lambda X` agrees with `lambda` of the underlying scheme of any surjective
étale presentation of `X`. -/
theorem lambda_spec {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (p : ofOver U ⟶ X) [Etale p] (hp : Function.Surjective (Points.map p)) :
    lambda X = Scheme.lambda U.left :=
  sorry

/-- On a scheme viewed as an algebraic space over `S`, `lambda` recovers the
scheme-level cardinal. -/
theorem lambda_ofOver {S : Scheme.{u}} (U : Over S) :
    lambda (ofOver U) = Scheme.lambda U.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
