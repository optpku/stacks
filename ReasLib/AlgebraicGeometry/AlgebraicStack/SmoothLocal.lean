module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic

/-!
# Smooth-local transfer for algebraic stacks

A smooth-local property of schemes transfers between surjective smooth scheme
atlases, arbitrary smooth scheme maps, and the corresponding algebraic-space
tests of an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists a scheme `U` over `S` and a surjective smooth morphism
`GroupoidsOver.slice U ⟶ X` such that `U` has property `P`. -/
def existsSurjectiveSmooth {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] : Prop :=
  ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
    Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ P U.left

/-- `existsSurjectiveSmooth P X` is the existence of a surjective smooth scheme
atlas with property `P`. -/
theorem existsSurjectiveSmooth_def {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] :
    existsSurjectiveSmooth P X ↔
      ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ P U.left :=
  Iff.rfl

namespace existsSurjectiveSmooth

/-- A surjective smooth scheme atlas with property `P` witnesses
`existsSurjectiveSmooth P X`. -/
theorem of {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} (p : GroupoidsOver.slice U ⟶ X)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p] (hP : P U.left) :
    existsSurjectiveSmooth P X :=
  ⟨U, p, inferInstance, inferInstance, hP⟩

/-- An algebraic stack satisfying `existsSurjectiveSmooth P X` admits a
surjective smooth scheme atlas with property `P`. -/
theorem spec {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (h : existsSurjectiveSmooth P X) :
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ P U.left :=
  h

end existsSurjectiveSmooth

/-- Every smooth morphism from a scheme `U` over `S` to `X` has `P U.left`. -/
def forallSmooth {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] : Prop :=
  ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
    Groupoids.Hom.Smooth p → P U.left

/-- `forallSmooth P X` is the statement that every smooth morphism from a scheme
to `X` has property `P` on the source. -/
theorem forallSmooth_def {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] :
    forallSmooth P X ↔
      ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p → P U.left :=
  Iff.rfl

namespace forallSmooth

/-- The universal smooth-scheme condition witnesses `forallSmooth P X`. -/
theorem of {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    (h : ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p → P U.left) : forallSmooth P X :=
  h

/-- If `forallSmooth P X`, then every smooth morphism from a scheme `U` to `X`
has `P U.left`. -/
theorem spec {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (h : forallSmooth P X) {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) (hp : Groupoids.Hom.Smooth p) : P U.left :=
  h U p hp

end forallSmooth

/-- There exists an algebraic space `U` over `S` and a surjective smooth morphism
`U.toGroupoids ⟶ X` such that `U` has property `P`. -/
def existsSurjectiveSmoothSpace {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] : Prop :=
  ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
    Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
      AlgebraicSpace.existsSurjectiveEtale P U

/-- `existsSurjectiveSmoothSpace P X` is the existence of a surjective smooth
algebraic-space atlas with property `P`. -/
theorem existsSurjectiveSmoothSpace_def {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) (X : GroupoidsOver S) [AlgebraicStack X] :
    existsSurjectiveSmoothSpace P X ↔
      ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
          AlgebraicSpace.existsSurjectiveEtale P U :=
  Iff.rfl

namespace existsSurjectiveSmoothSpace

/-- A surjective smooth algebraic-space atlas with property `P` witnesses
`existsSurjectiveSmoothSpace P X`. -/
theorem of {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {U : AlgebraicSpace S} (p : U.toGroupoids ⟶ X)
    [Groupoids.Hom.Smooth p] [Groupoids.Hom.Surjective p]
    (hP : AlgebraicSpace.existsSurjectiveEtale P U) :
    existsSurjectiveSmoothSpace P X :=
  ⟨U, p, inferInstance, inferInstance, hP⟩

/-- An algebraic stack satisfying `existsSurjectiveSmoothSpace P X` admits a
surjective smooth algebraic-space atlas with property `P`. -/
theorem spec {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsSurjectiveSmoothSpace P X) :
    ∃ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        AlgebraicSpace.existsSurjectiveEtale P U :=
  h

end existsSurjectiveSmoothSpace

/-- Every smooth morphism from an algebraic space `U` over `S` to `X` has
property `P` on `U`. -/
def forallSmoothSpace {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] : Prop :=
  ∀ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
    Groupoids.Hom.Smooth p → AlgebraicSpace.existsSurjectiveEtale P U

/-- `forallSmoothSpace P X` is the statement that every smooth morphism from an
algebraic space to `X` has property `P` on the source. -/
theorem forallSmoothSpace_def {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : GroupoidsOver S) [AlgebraicStack X] :
    forallSmoothSpace P X ↔
      ∀ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
        Groupoids.Hom.Smooth p → AlgebraicSpace.existsSurjectiveEtale P U :=
  Iff.rfl

namespace forallSmoothSpace

/-- The universal smooth algebraic-space condition witnesses
`forallSmoothSpace P X`. -/
theorem of {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    (h : ∀ (U : AlgebraicSpace S) (p : U.toGroupoids ⟶ X),
      Groupoids.Hom.Smooth p → AlgebraicSpace.existsSurjectiveEtale P U) :
    forallSmoothSpace P X :=
  h

/-- If `forallSmoothSpace P X`, then every smooth morphism from an algebraic
space `U` to `X` has property `P` on `U`. -/
theorem spec {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (h : forallSmoothSpace P X)
    {U : AlgebraicSpace S} (p : U.toGroupoids ⟶ X)
    (hp : Groupoids.Hom.Smooth p) : AlgebraicSpace.existsSurjectiveEtale P U :=
  h U p hp

end forallSmoothSpace

/-- Let `P` be a property of schemes which is local in the
smooth topology, and let `X` be an algebraic stack. There exists a scheme `U`
and a surjective smooth morphism `U ⟶ X` with `P U.left` if and only if every
smooth morphism `U ⟶ X` from a scheme has `P U.left`. -/
theorem existsSurjectiveSmooth_iff_forallSmooth {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X] :
    existsSurjectiveSmooth P X ↔ forallSmooth P X :=
  sorry

/-- Let `P` be a property of schemes which is local in the
smooth topology, and let `X` be an algebraic stack. There exists a surjective
smooth scheme atlas with property `P` if and only if there exists a surjective
smooth algebraic-space atlas with property `P`. -/
theorem existsSurjectiveSmooth_iff_existsSurjectiveSmoothSpace {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X] :
    existsSurjectiveSmooth P X ↔ existsSurjectiveSmoothSpace P X :=
  sorry

/-- Let `P` be a property of schemes which is local in the
smooth topology, and let `X` be an algebraic stack. There exists an algebraic
space `U` and a surjective smooth morphism `U ⟶ X` such that `U` has property
`P` if and only if every smooth morphism `U ⟶ X` from an algebraic space has
property `P` on the source. -/
theorem existsSurjectiveSmoothSpace_iff_forallSmoothSpace {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (X : GroupoidsOver S) [AlgebraicStack X] :
    existsSurjectiveSmoothSpace P X ↔ forallSmoothSpace P X :=
  sorry

/-- If `X` is a scheme `U` over `S`, then
`existsSurjectiveSmooth P (GroupoidsOver.slice U)` is equivalent to `P U.left`. -/
theorem existsSurjectiveSmooth_slice {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (U : Over S) : existsSurjectiveSmooth P (GroupoidsOver.slice U) ↔ P U.left :=
  sorry

/-- If `X` is an algebraic space `F` over `S`, then
`existsSurjectiveSmooth P F.toGroupoids` is equivalent to `F` having property
`P`. -/
theorem existsSurjectiveSmooth_toGroupoids {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    (F : AlgebraicSpace S) :
    existsSurjectiveSmooth P F.toGroupoids ↔
      AlgebraicSpace.existsSurjectiveEtale P F :=
  sorry

/-- If `U` is a scheme over `S`, then every smooth morphism from a scheme to
`GroupoidsOver.slice U` has property `P` if and only if `U.left` has property
`P`. -/
theorem forallSmooth_slice {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.bigSmoothPrecoverage] (U : Over S) :
    forallSmooth P (GroupoidsOver.slice U) ↔ P U.left :=
  sorry

/-- The smooth-local atlas criterion transports along an equivalence to a
scheme slice. -/
theorem existsSurjectiveSmooth_equivalence {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (e : X ≌ GroupoidsOver.slice U) :
    existsSurjectiveSmooth P X ↔ P U.left :=
  sorry

/-- If `P` is also étale-local, the algebraic-space specialization of
`existsSurjectiveSmooth` is `AlgebraicSpace.hasEtaleLocal`. -/
theorem existsSurjectiveSmooth_hasEtaleLocal {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.bigSmoothPrecoverage]
    [P.IsLocal Scheme.etalePrecoverage] (F : AlgebraicSpace S) :
    existsSurjectiveSmooth P F.toGroupoids ↔
      AlgebraicSpace.hasEtaleLocal P F :=
  sorry

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
