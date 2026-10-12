/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap68.Lemma_68_4_2_Fibre
public import stacks_project.Chap68.Definition_68_3_1_FiberDegree
public import stacks_project.Chap68.Lemma_68_4_3_Fibre

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
  sorry

/-- Membership in `selfPullbackFibreOver φ x` is the point-mapping equation along
`pullback.fst φ φ ≫ φ`. -/
theorem mem_selfPullbackFibreOver_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (φ : ofOver U ⟶ X) (x : Points X) (w : Points (pullback φ φ)) :
    w ∈ selfPullbackFibreOver φ x ↔ Points.map (pullback.fst φ φ ≫ φ) w = x :=
  sorry

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
  sorry

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
  sorry

namespace existsMonoFieldValuedFiniteNonemptyFibre

/-- A monomorphism `Spec(k) ⟶ X` in the class of `x` whose represented fibre is a
finite nonempty scheme over `k` witnesses
`existsMonoFieldValuedFiniteNonemptyFibre`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) {x : Points X} (p : FieldValuedPoint X) [Mono p.hom]
    (hx : Points.mk p = x) (hfin : IsFinite (fieldValuedPointPullbackSnd φ p))
    (hne : Nonempty (fieldValuedPointPullback φ p).left) :
    existsMonoFieldValuedFiniteNonemptyFibre φ x :=
  sorry

/-- `existsMonoFieldValuedFiniteNonemptyFibre φ x` supplies a monomorphism from
the spectrum of a field in the class of `x` whose represented fibre is a finite
nonempty scheme over that field. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) {x : Points X}
    (h : existsMonoFieldValuedFiniteNonemptyFibre φ x) :
    ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x ∧
      IsFinite (fieldValuedPointPullbackSnd φ p) ∧
        Nonempty (fieldValuedPointPullback φ p).left :=
  sorry

end existsMonoFieldValuedFiniteNonemptyFibre

/-- `existsMonoFieldValuedFiniteNonemptyFibre φ x` implies existence of a
monomorphism from the spectrum of a field in the class of `x`. -/
theorem existsMonoFieldValuedFiniteNonemptyFibre.existsMonoFieldValuedPoint
    {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
    {x : Points X} (h : existsMonoFieldValuedFiniteNonemptyFibre φ x) :
    existsMonoFieldValuedPoint X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
