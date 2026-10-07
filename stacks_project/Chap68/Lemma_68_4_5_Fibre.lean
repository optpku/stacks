module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap68.Lemma_68_4_2_Fibre
public import stacks_project.Chap68.Lemma_68_4_4_Fibre

/-!
# Pointwise finiteness and quasi-compactness tests above a point

This module records six equivalent pointwise tests at a point of an algebraic
space: affine étale charts with finite `|U|` and `|U ×_X U|` fibres, existence of
an étale scheme covering with those finite fibres, existence of a monomorphism
from the spectrum of a field whose affine étale fibres are finite over the field,
and the quasi-compact field-valued-point formulations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every étale morphism from an affine scheme to `X` has finite fibres of both
`|U| → |X|` and `|U ×_X U| → |X|` over `x`. -/
def forallAffineEtaleFiniteAbove {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
    finiteFibreOver φ x ∧ selfPullbackFibreFiniteOver φ x

/-- `forallAffineEtaleFiniteAbove X x` unpacks to finiteness of both fibres over
`x` for every affine étale morphism to `X`. -/
theorem forallAffineEtaleFiniteAbove_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) :
    forallAffineEtaleFiniteAbove X x ↔
      ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
        finiteFibreOver φ x ∧ selfPullbackFibreFiniteOver φ x :=
  sorry

namespace forallAffineEtaleFiniteAbove

/-- A universal finite-fibre condition on affine étale morphisms to `X` witnesses
`forallAffineEtaleFiniteAbove`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      finiteFibreOver φ x ∧ selfPullbackFibreFiniteOver φ x) :
    forallAffineEtaleFiniteAbove X x :=
  sorry

/-- Under `forallAffineEtaleFiniteAbove X x`, every étale morphism from an affine
scheme to `X` has finite fibres of both `|U| → |X|` and `|U ×_X U| → |X|` over
`x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : forallAffineEtaleFiniteAbove X x) (U : Over S) [IsAffine U.left]
    (φ : ofOver U ⟶ X) [Etale φ] :
    finiteFibreOver φ x ∧ selfPullbackFibreFiniteOver φ x :=
  sorry

end forallAffineEtaleFiniteAbove

/-- There is a family of étale morphisms from schemes covering `X` with finite
fibres of both `|U i| → |X|` and `|U i ×_X U i| → |X|` over `x`. -/
def existsEtaleCoverFiniteAbove {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
    (∀ i, Etale (φ i)) ∧
      (∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i))) ∧
        ∀ i, finiteFibreOver (φ i) x ∧ selfPullbackFibreFiniteOver (φ i) x

/-- `existsEtaleCoverFiniteAbove X x` unpacks to an étale family of schemes
covering the points of `X` with both fibres finite over `x`. -/
theorem existsEtaleCoverFiniteAbove_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) :
    existsEtaleCoverFiniteAbove X x ↔
      ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
        (∀ i, Etale (φ i)) ∧
          (∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i))) ∧
            ∀ i, finiteFibreOver (φ i) x ∧ selfPullbackFibreFiniteOver (φ i) x :=
  sorry

namespace existsEtaleCoverFiniteAbove

/-- An étale family of schemes whose images cover the points of `X` and whose
`|U i|` and `|U i ×_X U i|` fibres over `x` are finite witnesses
`existsEtaleCoverFiniteAbove`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} {I : Type u}
    {U : I → Over S} (φ : (i : I) → ofOver (U i) ⟶ X) [∀ i, Etale (φ i)]
    (hcover : ∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i)))
    (hfin : ∀ i, finiteFibreOver (φ i) x ∧ selfPullbackFibreFiniteOver (φ i) x) :
    existsEtaleCoverFiniteAbove X x :=
  sorry

/-- `existsEtaleCoverFiniteAbove X x` supplies an étale family of schemes covering
the points of `X` with both fibres finite over `x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsEtaleCoverFiniteAbove X x) :
    ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
      (∀ i, Etale (φ i)) ∧
        (∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i))) ∧
          ∀ i, finiteFibreOver (φ i) x ∧ selfPullbackFibreFiniteOver (φ i) x :=
  sorry

end existsEtaleCoverFiniteAbove

/-- The covering clause of `existsEtaleCoverFiniteAbove` is equivalent to
surjectivity of the induced coproduct morphism `∐ φ i`. -/
theorem existsEtaleCoverFiniteAbove_iff_coproductDesc {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) :
    existsEtaleCoverFiniteAbove X x ↔
      ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
        (∀ i, Etale (φ i)) ∧ Surjective (coproductDesc φ) ∧
          ∀ i, finiteFibreOver (φ i) x ∧ selfPullbackFibreFiniteOver (φ i) x :=
  sorry

/-- There is a monomorphism `Spec(k) ⟶ X` in the class of `x` such that
`Spec(k) ×_X U` is a finite scheme over `k` for every affine étale morphism
`U → X`. -/
def existsMonoFieldValuedFiniteAffineFibres {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) : Prop :=
  ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x ∧
    ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      IsFinite (fieldValuedPointPullbackSnd φ p)

/-- `existsMonoFieldValuedFiniteAffineFibres X x` unpacks to a monomorphism from
the spectrum of a field in the class of `x` whose affine étale fibres are finite
over that field. -/
theorem existsMonoFieldValuedFiniteAffineFibres_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) :
    existsMonoFieldValuedFiniteAffineFibres X x ↔
      ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x ∧
        ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
          IsFinite (fieldValuedPointPullbackSnd φ p) :=
  sorry

namespace existsMonoFieldValuedFiniteAffineFibres

/-- A monomorphism `Spec(k) ⟶ X` in the class of `x` whose affine étale fibres
are finite over `k` witnesses `existsMonoFieldValuedFiniteAffineFibres`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (p : FieldValuedPoint X) [Mono p.hom] (hx : Points.mk p = x)
    (hfin : ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      IsFinite (fieldValuedPointPullbackSnd φ p)) :
    existsMonoFieldValuedFiniteAffineFibres X x :=
  sorry

/-- `existsMonoFieldValuedFiniteAffineFibres X x` supplies a monomorphism from
the spectrum of a field in the class of `x` whose affine étale fibres are finite
over that field. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsMonoFieldValuedFiniteAffineFibres X x) :
    ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x ∧
      ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
        IsFinite (fieldValuedPointPullbackSnd φ p) :=
  sorry

end existsMonoFieldValuedFiniteAffineFibres

/-- `existsMonoFieldValuedFiniteAffineFibres X x` implies existence of a
monomorphism from the spectrum of a field in the class of `x`. -/
theorem existsMonoFieldValuedFiniteAffineFibres.existsMonoFieldValuedPoint
    {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsMonoFieldValuedFiniteAffineFibres X x) :
    existsMonoFieldValuedPoint X x :=
  sorry

/-- There is a quasi-compact monomorphism from the spectrum of a field in the
equivalence class of `x`. -/
def existsQuasiCompactMonoFieldValuedPoint {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) : Prop :=
  ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Mono p.hom ∧ Points.mk p = x

/-- `existsQuasiCompactMonoFieldValuedPoint X x` unpacks to a quasi-compact
monomorphism from the spectrum of a field in the class of `x`. -/
theorem existsQuasiCompactMonoFieldValuedPoint_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) :
    existsQuasiCompactMonoFieldValuedPoint X x ↔
      ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Mono p.hom ∧ Points.mk p = x :=
  sorry

namespace existsQuasiCompactMonoFieldValuedPoint

/-- A quasi-compact monomorphism `Spec(k) ⟶ X` in the class of `x` witnesses
`existsQuasiCompactMonoFieldValuedPoint`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (p : FieldValuedPoint X) [QuasiCompact p.hom] [Mono p.hom]
    (hx : Points.mk p = x) : existsQuasiCompactMonoFieldValuedPoint X x :=
  sorry

/-- `existsQuasiCompactMonoFieldValuedPoint X x` supplies a quasi-compact
monomorphism from the spectrum of a field in the class of `x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsQuasiCompactMonoFieldValuedPoint X x) :
    ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Mono p.hom ∧ Points.mk p = x :=
  sorry

end existsQuasiCompactMonoFieldValuedPoint

/-- `existsQuasiCompactMonoFieldValuedPoint X x` implies existence of a
monomorphism from the spectrum of a field in the class of `x`. -/
theorem existsQuasiCompactMonoFieldValuedPoint.existsMonoFieldValuedPoint
    {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsQuasiCompactMonoFieldValuedPoint X x) :
    existsMonoFieldValuedPoint X x :=
  sorry

/-- There is a quasi-compact morphism from the spectrum of a field in the
equivalence class of `x`. -/
def existsQuasiCompactFieldValuedPoint {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Points.mk p = x

/-- `existsQuasiCompactFieldValuedPoint X x` unpacks to a quasi-compact morphism
from the spectrum of a field in the class of `x`. -/
theorem existsQuasiCompactFieldValuedPoint_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) :
    existsQuasiCompactFieldValuedPoint X x ↔
      ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Points.mk p = x :=
  sorry

namespace existsQuasiCompactFieldValuedPoint

/-- A quasi-compact morphism `Spec(k) ⟶ X` in the class of `x` witnesses
`existsQuasiCompactFieldValuedPoint`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (p : FieldValuedPoint X) [QuasiCompact p.hom] (hx : Points.mk p = x) :
    existsQuasiCompactFieldValuedPoint X x :=
  sorry

/-- `existsQuasiCompactFieldValuedPoint X x` supplies a quasi-compact morphism
from the spectrum of a field in the class of `x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsQuasiCompactFieldValuedPoint X x) :
    ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Points.mk p = x :=
  sorry

end existsQuasiCompactFieldValuedPoint

/-- `existsQuasiCompactMonoFieldValuedPoint X x` implies existence of a
quasi-compact field-valued point in the class of `x`. -/
theorem existsQuasiCompactMonoFieldValuedPoint.existsQuasiCompactFieldValuedPoint
    {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsQuasiCompactMonoFieldValuedPoint X x) :
    existsQuasiCompactFieldValuedPoint X x :=
  sorry

/-- Every field-valued point in the class of `x` is a quasi-compact morphism. -/
def forallFieldValuedPointQuasiCompact {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∀ p : FieldValuedPoint X, Points.mk p = x → QuasiCompact p.hom

/-- `forallFieldValuedPointQuasiCompact X x` unpacks to quasi-compactness of every
field-valued point in the class of `x`. -/
theorem forallFieldValuedPointQuasiCompact_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) :
    forallFieldValuedPointQuasiCompact X x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x → QuasiCompact p.hom :=
  sorry

namespace forallFieldValuedPointQuasiCompact

/-- A universal quasi-compactness condition on field-valued points in the class of
`x` witnesses `forallFieldValuedPointQuasiCompact`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : ∀ p : FieldValuedPoint X, Points.mk p = x → QuasiCompact p.hom) :
    forallFieldValuedPointQuasiCompact X x :=
  sorry

/-- Under `forallFieldValuedPointQuasiCompact X x`, every field-valued point in
the class of `x` is quasi-compact. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : forallFieldValuedPointQuasiCompact X x) {p : FieldValuedPoint X}
    (hp : Points.mk p = x) : QuasiCompact p.hom :=
  sorry

end forallFieldValuedPointQuasiCompact

/-- Affine étale finite fibres over `x` are equivalent to existence of an étale
scheme covering with both fibres finite over `x`. -/
theorem forallAffineEtaleFiniteAbove_iff_existsEtaleCoverFiniteAbove
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    forallAffineEtaleFiniteAbove X x ↔ existsEtaleCoverFiniteAbove X x :=
  sorry

/-- Affine étale finite fibres over `x` are equivalent to existence of a
monomorphism from the spectrum of a field in the class of `x` with finite affine
étale fibres over that field. -/
theorem forallAffineEtaleFiniteAbove_iff_existsMonoFieldValuedFiniteAffineFibres
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    forallAffineEtaleFiniteAbove X x ↔
      existsMonoFieldValuedFiniteAffineFibres X x :=
  sorry

namespace existsMonoFieldValuedFiniteAffineFibres

/-- Existence of a monomorphism from the spectrum of a field with finite affine
étale fibres is equivalent to existence of a quasi-compact monomorphism in the
class of `x`. -/
theorem iff_existsQuasiCompactMonoFieldValuedPoint
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    existsMonoFieldValuedFiniteAffineFibres X x ↔
      existsQuasiCompactMonoFieldValuedPoint X x :=
  sorry

end existsMonoFieldValuedFiniteAffineFibres

namespace finiteAbove

/-- Existence of a quasi-compact monomorphism in the class of `x` is equivalent to
existence of a quasi-compact field-valued point in that class. -/
theorem quasiCompactMono_iff_quasiCompact
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    existsQuasiCompactMonoFieldValuedPoint X x ↔
      existsQuasiCompactFieldValuedPoint X x :=
  sorry

/-- Existence of a quasi-compact monomorphism in the class of `x` is equivalent to
quasi-compactness of every field-valued point in that class. -/
theorem quasiCompactMono_iff_forallQuasiCompact
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    existsQuasiCompactMonoFieldValuedPoint X x ↔
      forallFieldValuedPointQuasiCompact X x :=
  sorry

end finiteAbove

end AlgebraicGeometry.AlgebraicSpace
