/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteFibers
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.RelationFiniteFibre

/-!
# Fibres of a self-pullback over a point of an algebraic space

The fibre of `|U ×_X U| → |X|` over a point is the preimage of that point under
the composite of a self-pullback projection with the chart morphism. This module
records that fibre, its finiteness, and the equivalent existence of a
monomorphism from the spectrum of a field in the point class whose represented
fibre is a finite nonempty scheme over the field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre of `|U ×_X U| → |X|` over `x`, for the chosen self-pullback of `φ`. -/
def selfPullbackFibreOver {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (x : Points X) : Set (Points (pullback φ φ)) :=
  Points.map (pullback.fst φ φ ≫ φ) ⁻¹' {x}

/-- `selfPullbackFibreOver φ x` is the preimage of `x` under
`Points.map (pullback.fst φ φ ≫ φ)`. -/
theorem selfPullbackFibreOver_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (φ : ofOver U ⟶ X) (x : Points X) :
    selfPullbackFibreOver φ x = Points.map (pullback.fst φ φ ≫ φ) ⁻¹' {x} :=
  rfl

/-- Membership in `selfPullbackFibreOver φ x` is the point-mapping equation along
`pullback.fst φ φ ≫ φ`. -/
theorem mem_selfPullbackFibreOver_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (φ : ofOver U ⟶ X) (x : Points X) (w : Points (pullback φ φ)) :
    w ∈ selfPullbackFibreOver φ x ↔ Points.map (pullback.fst φ φ ≫ φ) w = x :=
  Iff.rfl

/-- The chosen self-pullback fibre of `|U ×_X U| → |X|` over `x` agrees with the
preimage along `pullback.snd φ φ ≫ φ`. -/
theorem selfPullbackFibreOver_eq_snd {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (φ : ofOver U ⟶ X) (x : Points X) :
    selfPullbackFibreOver φ x = Points.map (pullback.snd φ φ ≫ φ) ⁻¹' {x} :=
  sorry

/-- The fibre of `|U ×_X U| → |X|` over `x` is finite. -/
def selfPullbackFibreFiniteOver {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (φ : ofOver U ⟶ X) (x : Points X) : Prop :=
  (selfPullbackFibreOver φ x).Finite

/-- `selfPullbackFibreFiniteOver φ x` is finiteness of `selfPullbackFibreOver φ x`. -/
theorem selfPullbackFibreFiniteOver_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (φ : ofOver U ⟶ X) (x : Points X) :
    selfPullbackFibreFiniteOver φ x ↔ (selfPullbackFibreOver φ x).Finite :=
  Iff.rfl

/-- Finiteness of the chosen self-pullback fibre over `x` is equivalent to
finiteness of the fibre of any `IsPullback` presentation of `U ×_X U`. -/
theorem selfPullbackFibreFiniteOver_iff_isPullback {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) {R : AlgebraicSpace S}
    (fst snd : R ⟶ ofOver U) (h : IsPullback fst snd φ φ) (x : Points X) :
    selfPullbackFibreFiniteOver φ x ↔ (Points.map (fst ≫ φ) ⁻¹' {x}).Finite :=
  sorry

/-- There is a monomorphism `Spec(k) ⟶ X` in the class of `x` whose represented
fibre `Spec(k) ×_X U` is a finite nonempty scheme over `k`. -/
def existsMonoFieldValuedFiniteNonemptyFibre {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) (x : Points X) : Prop :=
  ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x ∧
    IsFinite (fieldValuedPointPullbackSnd φ p) ∧
      Nonempty (fieldValuedPointPullback φ p).left

/-- `existsMonoFieldValuedFiniteNonemptyFibre φ x` unpacks to a monomorphism from
the spectrum of a field in the class of `x` whose represented fibre is a finite
nonempty scheme over that field. -/
theorem existsMonoFieldValuedFiniteNonemptyFibre_iff {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) (x : Points X) :
    existsMonoFieldValuedFiniteNonemptyFibre φ x ↔
      ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x ∧
        IsFinite (fieldValuedPointPullbackSnd φ p) ∧
          Nonempty (fieldValuedPointPullback φ p).left :=
  Iff.rfl

namespace existsMonoFieldValuedFiniteNonemptyFibre

/-- A monomorphism `Spec(k) ⟶ X` in the class of `x` whose represented fibre is a
finite nonempty scheme over `k` witnesses
`existsMonoFieldValuedFiniteNonemptyFibre`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) {x : Points X} (p : FieldValuedPoint X) [Mono p.hom]
    (hx : Points.mk p = x) (hfin : IsFinite (fieldValuedPointPullbackSnd φ p))
    (hne : Nonempty (fieldValuedPointPullback φ p).left) :
    existsMonoFieldValuedFiniteNonemptyFibre φ x :=
  ⟨p, inferInstance, hx, hfin, hne⟩

/-- `existsMonoFieldValuedFiniteNonemptyFibre φ x` supplies a monomorphism from
the spectrum of a field in the class of `x` whose represented fibre is a finite
nonempty scheme over that field. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) {x : Points X}
    (h : existsMonoFieldValuedFiniteNonemptyFibre φ x) :
    ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x ∧
      IsFinite (fieldValuedPointPullbackSnd φ p) ∧
        Nonempty (fieldValuedPointPullback φ p).left :=
  h

end existsMonoFieldValuedFiniteNonemptyFibre

/-- `existsMonoFieldValuedFiniteNonemptyFibre φ x` implies existence of a
monomorphism from the spectrum of a field in the class of `x`. -/
theorem existsMonoFieldValuedFiniteNonemptyFibre.existsMonoFieldValuedPoint
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
    {x : Points X} (h : existsMonoFieldValuedFiniteNonemptyFibre φ x) :
    existsMonoFieldValuedPoint X x :=
  h.elim fun p hp ↦ ⟨p, hp.1, hp.2.1⟩

/-- For an étale morphism from a scheme to an algebraic space, image membership
and finiteness of the chart and self-pullback fibres over a point are equivalent
to a monomorphic field-valued representative whose scheme fibre is finite and
nonempty over its field. -/
theorem etaleChartFiniteAbove_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] (x : Points X) :
    (x ∈ Set.range (Points.mapOfOver φ) ∧ finiteFibreOver φ x ∧
      selfPullbackFibreFiniteOver φ x) ↔
      existsMonoFieldValuedFiniteNonemptyFibre φ x :=
  sorry

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
  Iff.rfl

namespace forallAffineEtaleFiniteAbove

/-- A universal finite-fibre condition on affine étale morphisms to `X` witnesses
`forallAffineEtaleFiniteAbove`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      finiteFibreOver φ x ∧ selfPullbackFibreFiniteOver φ x) :
    forallAffineEtaleFiniteAbove X x :=
  h

/-- Under `forallAffineEtaleFiniteAbove X x`, every étale morphism from an affine
scheme to `X` has finite fibres of both `|U| → |X|` and `|U ×_X U| → |X|` over
`x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : forallAffineEtaleFiniteAbove X x) (U : Over S) [IsAffine U.left]
    (φ : ofOver U ⟶ X) [Etale φ] :
    finiteFibreOver φ x ∧ selfPullbackFibreFiniteOver φ x :=
  h U φ

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
  Iff.rfl

namespace existsEtaleCoverFiniteAbove

/-- An étale family of schemes whose images cover the points of `X` and whose
`|U i|` and `|U i ×_X U i|` fibres over `x` are finite witnesses
`existsEtaleCoverFiniteAbove`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} {I : Type u}
    {U : I → Over S} (φ : (i : I) → ofOver (U i) ⟶ X) [∀ i, Etale (φ i)]
    (hcover : ∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i)))
    (hfin : ∀ i, finiteFibreOver (φ i) x ∧ selfPullbackFibreFiniteOver (φ i) x) :
    existsEtaleCoverFiniteAbove X x :=
  ⟨I, U, φ, fun _ ↦ inferInstance, hcover, hfin⟩

/-- `existsEtaleCoverFiniteAbove X x` supplies an étale family of schemes covering
the points of `X` with both fibres finite over `x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsEtaleCoverFiniteAbove X x) :
    ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
      (∀ i, Etale (φ i)) ∧
        (∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i))) ∧
          ∀ i, finiteFibreOver (φ i) x ∧ selfPullbackFibreFiniteOver (φ i) x :=
  h

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
  Iff.rfl

namespace existsMonoFieldValuedFiniteAffineFibres

/-- A monomorphism `Spec(k) ⟶ X` in the class of `x` whose affine étale fibres
are finite over `k` witnesses `existsMonoFieldValuedFiniteAffineFibres`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (p : FieldValuedPoint X) [Mono p.hom] (hx : Points.mk p = x)
    (hfin : ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      IsFinite (fieldValuedPointPullbackSnd φ p)) :
    existsMonoFieldValuedFiniteAffineFibres X x :=
  ⟨p, inferInstance, hx, hfin⟩

/-- `existsMonoFieldValuedFiniteAffineFibres X x` supplies a monomorphism from
the spectrum of a field in the class of `x` whose affine étale fibres are finite
over that field. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsMonoFieldValuedFiniteAffineFibres X x) :
    ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x ∧
      ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
        IsFinite (fieldValuedPointPullbackSnd φ p) :=
  h

end existsMonoFieldValuedFiniteAffineFibres

/-- `existsMonoFieldValuedFiniteAffineFibres X x` implies existence of a
monomorphism from the spectrum of a field in the class of `x`. -/
theorem existsMonoFieldValuedFiniteAffineFibres.existsMonoFieldValuedPoint
    {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsMonoFieldValuedFiniteAffineFibres X x) :
    existsMonoFieldValuedPoint X x :=
  h.elim fun p hp ↦ ⟨p, hp.1, hp.2.1⟩

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
  Iff.rfl

namespace existsQuasiCompactMonoFieldValuedPoint

/-- A quasi-compact monomorphism `Spec(k) ⟶ X` in the class of `x` witnesses
`existsQuasiCompactMonoFieldValuedPoint`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (p : FieldValuedPoint X) [QuasiCompact p.hom] [Mono p.hom]
    (hx : Points.mk p = x) : existsQuasiCompactMonoFieldValuedPoint X x :=
  ⟨p, inferInstance, inferInstance, hx⟩

/-- `existsQuasiCompactMonoFieldValuedPoint X x` supplies a quasi-compact
monomorphism from the spectrum of a field in the class of `x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsQuasiCompactMonoFieldValuedPoint X x) :
    ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Mono p.hom ∧ Points.mk p = x :=
  h

end existsQuasiCompactMonoFieldValuedPoint

/-- `existsQuasiCompactMonoFieldValuedPoint X x` implies existence of a
monomorphism from the spectrum of a field in the class of `x`. -/
theorem existsQuasiCompactMonoFieldValuedPoint.existsMonoFieldValuedPoint
    {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsQuasiCompactMonoFieldValuedPoint X x) :
    existsMonoFieldValuedPoint X x :=
  h.elim fun p hp ↦ ⟨p, hp.2.1, hp.2.2⟩

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
  Iff.rfl

namespace existsQuasiCompactFieldValuedPoint

/-- A quasi-compact morphism `Spec(k) ⟶ X` in the class of `x` witnesses
`existsQuasiCompactFieldValuedPoint`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (p : FieldValuedPoint X) [QuasiCompact p.hom] (hx : Points.mk p = x) :
    existsQuasiCompactFieldValuedPoint X x :=
  ⟨p, inferInstance, hx⟩

/-- `existsQuasiCompactFieldValuedPoint X x` supplies a quasi-compact morphism
from the spectrum of a field in the class of `x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsQuasiCompactFieldValuedPoint X x) :
    ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Points.mk p = x :=
  h

end existsQuasiCompactFieldValuedPoint

/-- `existsQuasiCompactMonoFieldValuedPoint X x` implies existence of a
quasi-compact field-valued point in the class of `x`. -/
theorem existsQuasiCompactMonoFieldValuedPoint.existsQuasiCompactFieldValuedPoint
    {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsQuasiCompactMonoFieldValuedPoint X x) :
    existsQuasiCompactFieldValuedPoint X x :=
  h.elim fun p hp ↦ ⟨p, hp.1, hp.2.2⟩

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
  Iff.rfl

namespace forallFieldValuedPointQuasiCompact

/-- A universal quasi-compactness condition on field-valued points in the class of
`x` witnesses `forallFieldValuedPointQuasiCompact`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : ∀ p : FieldValuedPoint X, Points.mk p = x → QuasiCompact p.hom) :
    forallFieldValuedPointQuasiCompact X x :=
  h

/-- Under `forallFieldValuedPointQuasiCompact X x`, every field-valued point in
the class of `x` is quasi-compact. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : forallFieldValuedPointQuasiCompact X x) {p : FieldValuedPoint X}
    (hp : Points.mk p = x) : QuasiCompact p.hom :=
  h p hp

end forallFieldValuedPointQuasiCompact

/-- For a point of an algebraic space, finiteness of affine étale chart and
self-pullback fibres, an étale covering with finite fibres, a monomorphic
field-valued representative with finite affine étale fibres, and the three
quasi-compactness conditions on field-valued representatives are equivalent. -/
theorem finiteAbove_tfae {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    List.TFAE
      [ forallAffineEtaleFiniteAbove X x
      , existsEtaleCoverFiniteAbove X x
      , existsMonoFieldValuedFiniteAffineFibres X x
      , existsQuasiCompactMonoFieldValuedPoint X x
      , existsQuasiCompactFieldValuedPoint X x
      , forallFieldValuedPointQuasiCompact X x ] :=
  sorry

/-- Affine étale finite fibres over `x` are equivalent to existence of an étale
scheme covering with both fibres finite over `x`. -/
theorem forallAffineEtaleFiniteAbove_iff_existsEtaleCoverFiniteAbove
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    forallAffineEtaleFiniteAbove X x ↔ existsEtaleCoverFiniteAbove X x :=
  (finiteAbove_tfae X x).out 0 1

/-- Affine étale finite fibres over `x` are equivalent to existence of a
monomorphism from the spectrum of a field in the class of `x` with finite affine
étale fibres over that field. -/
theorem forallAffineEtaleFiniteAbove_iff_existsMonoFieldValuedFiniteAffineFibres
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    forallAffineEtaleFiniteAbove X x ↔
      existsMonoFieldValuedFiniteAffineFibres X x :=
  (finiteAbove_tfae X x).out 0 2

namespace existsMonoFieldValuedFiniteAffineFibres

/-- Existence of a monomorphism from the spectrum of a field with finite affine
étale fibres is equivalent to existence of a quasi-compact monomorphism in the
class of `x`. -/
theorem iff_existsQuasiCompactMonoFieldValuedPoint
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    existsMonoFieldValuedFiniteAffineFibres X x ↔
      existsQuasiCompactMonoFieldValuedPoint X x :=
  (finiteAbove_tfae X x).out 2 3

end existsMonoFieldValuedFiniteAffineFibres

namespace finiteAbove

/-- Existence of a quasi-compact monomorphism in the class of `x` is equivalent to
existence of a quasi-compact field-valued point in that class. -/
theorem quasiCompactMono_iff_quasiCompact
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    existsQuasiCompactMonoFieldValuedPoint X x ↔
      existsQuasiCompactFieldValuedPoint X x :=
  (finiteAbove_tfae X x).out 3 4

/-- Existence of a quasi-compact monomorphism in the class of `x` is equivalent to
quasi-compactness of every field-valued point in that class. -/
theorem quasiCompactMono_iff_forallQuasiCompact
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    existsQuasiCompactMonoFieldValuedPoint X x ↔
      forallFieldValuedPointQuasiCompact X x :=
  (finiteAbove_tfae X x).out 3 5

end finiteAbove

end AlgebraicGeometry.AlgebraicSpace
