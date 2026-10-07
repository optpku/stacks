module

public import stacks_project.Chap100.Lemma_100_7_1

/-!
# Smooth-local scheme properties of algebraic stacks

A property of schemes that is local in the smooth topology descends to
algebraic stacks by testing it on a surjective smooth scheme atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack `X` has a smooth-local scheme property `P` when some
surjective smooth scheme atlas has property `P`. -/
def hasSmoothLocal {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.bigSmoothPrecoverage] (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop :=
  existsSurjectiveSmooth P X

/-- `hasSmoothLocal P X` is the existence of a surjective smooth scheme atlas
with property `P`. -/
theorem hasSmoothLocal_def {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.bigSmoothPrecoverage] (X : GroupoidsOver S)
    [AlgebraicStack X] :
    hasSmoothLocal P X ↔ existsSurjectiveSmooth P X :=
  Iff.rfl

namespace hasSmoothLocal

/-- A surjective smooth scheme atlas with property `P` witnesses
`hasSmoothLocal P X`. -/
theorem of {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}}
    [P.IsLocal Scheme.bigSmoothPrecoverage] {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} (p : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p] (hP : P U.left) :
    hasSmoothLocal P X :=
  existsSurjectiveSmooth.of p hP

/-- An algebraic stack satisfying `hasSmoothLocal P X` admits a surjective
smooth scheme atlas with property `P`. -/
theorem spec {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}}
    [P.IsLocal Scheme.bigSmoothPrecoverage] {X : GroupoidsOver S}
    [AlgebraicStack X] (h : hasSmoothLocal P X) :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ P U.left :=
  h

end hasSmoothLocal

/-- `X` has a smooth-local scheme property `P` if and only if every smooth
morphism from a scheme to `X` has property `P` on the source. -/
theorem hasSmoothLocal_iff_forallSmooth {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X] :
    hasSmoothLocal P X ↔ forallSmooth P X :=
  existsSurjectiveSmooth_iff_forallSmooth P X

/-- `X` has a smooth-local scheme property `P` if and only if some surjective
smooth algebraic-space atlas has property `P`. -/
theorem hasSmoothLocal_iff_existsSurjectiveSmoothSpace {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X] :
    hasSmoothLocal P X ↔ existsSurjectiveSmoothSpace P X :=
  existsSurjectiveSmooth_iff_existsSurjectiveSmoothSpace P X

/-- `X` has a smooth-local scheme property `P` if and only if every smooth
morphism from an algebraic space to `X` has property `P` on the source. -/
theorem hasSmoothLocal_iff_forallSmoothSpace {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X] :
    hasSmoothLocal P X ↔ forallSmoothSpace P X :=
  sorry

/-- If `X` is a scheme `U` over `S`, then `hasSmoothLocal P` on the slice of
`U` is equivalent to `P U.left`. -/
theorem hasSmoothLocal_slice {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.bigSmoothPrecoverage] (U : Over S) :
    hasSmoothLocal P (GroupoidsOver.slice U) ↔ P U.left :=
  existsSurjectiveSmooth_slice P U

/-- If `X` is an algebraic space `F` over `S` and `P` is also étale-local,
then `hasSmoothLocal P` on `F.toGroupoids` is equivalent to `F` having
property `P`. -/
theorem hasSmoothLocal_toGroupoids {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    [P.IsLocal Scheme.etalePrecoverage] (F : AlgebraicSpace S) :
    hasSmoothLocal P F.toGroupoids ↔ AlgebraicSpace.hasEtaleLocal P F :=
  existsSurjectiveSmooth_hasEtaleLocal P F

end AlgebraicGeometry.AlgebraicStack
