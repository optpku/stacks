module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

/-!
# Finite self-relation fibres over a point of an algebraic space

A point of an algebraic space has a finite self-relation fibre when an étale
morphism from a scheme has finite fibre of `|R| → |U| ×_{|X|} |U|` over a pair of
points mapping to it. This module records that pointwise condition, the matching
universal étale-chart test, and the equivalent field-valued-point formulations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre of `|R| → |U| × |U|` over the pair of scheme points `(u, u')`. -/
def relationFibre {S : Scheme.{u}} {U : Over S} {R : AlgebraicSpace S}
    (fst snd : R ⟶ ofOver U) (u u' : U.left) : Set (Points R) :=
  {w | Points.map fst w = ofOver.pointsEquiv U u ∧
      Points.map snd w = ofOver.pointsEquiv U u'}

/-- Membership in `relationFibre fst snd u u'` is the pair of point-mapping equations. -/
theorem relationFibre_iff {S : Scheme.{u}} {U : Over S} {R : AlgebraicSpace S}
    (fst snd : R ⟶ ofOver U) (u u' : U.left) (w : Points R) :
    w ∈ relationFibre fst snd u u' ↔
      Points.map fst w = ofOver.pointsEquiv U u ∧
        Points.map snd w = ofOver.pointsEquiv U u' :=
  sorry

/-- The fibre of `|U ×_X U| → |U| ×_{|X|} |U|` over `(u, u')` for the chosen
self-pullback of `φ`. -/
def selfRelationFibre {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (u u' : U.left) : Set (Points (pullback φ φ)) :=
  relationFibre (pullback.fst φ φ) (pullback.snd φ φ) u u'

/-- `selfRelationFibre φ u u'` is `relationFibre` of the chosen self-pullback legs. -/
theorem selfRelationFibre_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (u u' : U.left) :
    selfRelationFibre φ u u' =
      relationFibre (pullback.fst φ φ) (pullback.snd φ φ) u u' :=
  sorry

/-- Membership in the chosen self-relation fibre is the pair of point-mapping equations
along `pullback.fst` and `pullback.snd`. -/
theorem mem_selfRelationFibre_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (u u' : U.left) (w : Points (pullback φ φ)) :
    w ∈ selfRelationFibre φ u u' ↔
      Points.map (pullback.fst φ φ) w = ofOver.pointsEquiv U u ∧
        Points.map (pullback.snd φ φ) w = ofOver.pointsEquiv U u' :=
  sorry

/-- The chosen self-relation fibre of `φ` over `(u, u')` is finite. -/
def selfRelationFibreFinite {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (u u' : U.left) : Prop :=
  (selfRelationFibre φ u u').Finite

/-- `selfRelationFibreFinite φ u u'` is finiteness of `selfRelationFibre φ u u'`. -/
theorem selfRelationFibreFinite_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (φ : ofOver U ⟶ X) (u u' : U.left) :
    selfRelationFibreFinite φ u u' ↔ (selfRelationFibre φ u u').Finite :=
  sorry

/-- Finiteness of the chosen self-relation fibre is equivalent to finiteness of the fibre
of any `IsPullback` presentation of `U ×_X U`. -/
theorem selfRelationFibreFinite_iff_isPullback {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X) {R : AlgebraicSpace S}
    (fst snd : R ⟶ ofOver U) (h : IsPullback fst snd φ φ) (u u' : U.left) :
    selfRelationFibreFinite φ u u' ↔ (relationFibre fst snd u u').Finite :=
  sorry

/-- There exist an étale morphism from a scheme to `X` and points over `x` with finite
self-relation fibre. -/
def existsEtaleRelationFiniteFibre {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X), Etale φ ∧
    ∃ u u' : U.left, Points.mapOfOver φ u = x ∧ Points.mapOfOver φ u' = x ∧
      selfRelationFibreFinite φ u u'

namespace existsEtaleRelationFiniteFibre

/-- An étale morphism from a scheme with a pair of points over `x` whose self-relation
fibre is finite witnesses `existsEtaleRelationFiniteFibre`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] (u u' : U.left) (hu : Points.mapOfOver φ u = x)
    (hu' : Points.mapOfOver φ u' = x) (hfin : selfRelationFibreFinite φ u u') :
    existsEtaleRelationFiniteFibre X x :=
  sorry

/-- `existsEtaleRelationFiniteFibre X x` supplies an étale morphism from a scheme and
points over `x` with finite self-relation fibre. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsEtaleRelationFiniteFibre X x) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X), Etale φ ∧
      ∃ u u' : U.left, Points.mapOfOver φ u = x ∧ Points.mapOfOver φ u' = x ∧
        selfRelationFibreFinite φ u u' :=
  sorry

end existsEtaleRelationFiniteFibre

/-- Every étale morphism from a scheme to `X` has finite self-relation fibre over every
pair of points mapping to `x`. -/
def forallEtaleRelationFiniteFibre {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u u' : U.left),
    Points.mapOfOver φ u = x → Points.mapOfOver φ u' = x →
      selfRelationFibreFinite φ u u'

/-- `forallEtaleRelationFiniteFibre X x` means every étale morphism from a scheme to `X`
has finite self-relation fibre over every pair of points mapping to `x`. -/
theorem forallEtaleRelationFiniteFibre_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) :
    forallEtaleRelationFiniteFibre X x ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u u' : U.left),
        Points.mapOfOver φ u = x → Points.mapOfOver φ u' = x →
          selfRelationFibreFinite φ u u' :=
  sorry

namespace forallEtaleRelationFiniteFibre

/-- A universal finite self-relation-fibre condition on étale morphisms from schemes to
`X` witnesses `forallEtaleRelationFiniteFibre`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u u' : U.left),
      Points.mapOfOver φ u = x → Points.mapOfOver φ u' = x →
        selfRelationFibreFinite φ u u') :
    forallEtaleRelationFiniteFibre X x :=
  sorry

/-- Under `forallEtaleRelationFiniteFibre X x`, every étale morphism from a scheme to `X`
has finite self-relation fibre over every pair of points mapping to `x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : forallEtaleRelationFiniteFibre X x) (U : Over S) (φ : ofOver U ⟶ X)
    [Etale φ] (u u' : U.left) (hu : Points.mapOfOver φ u = x)
    (hu' : Points.mapOfOver φ u' = x) : selfRelationFibreFinite φ u u' :=
  sorry

end forallEtaleRelationFiniteFibre

/-- There is a field-valued point in the class of `x` whose self-relation projections are
étale and quasi-compact. -/
def existsEtaleQuasiCompactFieldSelfRelation {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∃ p : FieldValuedPoint X, Points.mk p = x ∧
    Etale (pullback.fst p.hom p.hom) ∧ QuasiCompact (pullback.fst p.hom p.hom) ∧
      Etale (pullback.snd p.hom p.hom) ∧ QuasiCompact (pullback.snd p.hom p.hom)

namespace existsEtaleQuasiCompactFieldSelfRelation

/-- A field-valued point in the class of `x` with étale quasi-compact self-relation
projections witnesses `existsEtaleQuasiCompactFieldSelfRelation`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (p : FieldValuedPoint X) (hx : Points.mk p = x)
    (hfst : Etale (pullback.fst p.hom p.hom) ∧
      QuasiCompact (pullback.fst p.hom p.hom))
    (hsnd : Etale (pullback.snd p.hom p.hom) ∧
      QuasiCompact (pullback.snd p.hom p.hom)) :
    existsEtaleQuasiCompactFieldSelfRelation X x :=
  sorry

/-- `existsEtaleQuasiCompactFieldSelfRelation X x` supplies a field-valued point in the
class of `x` whose self-relation projections are étale and quasi-compact. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsEtaleQuasiCompactFieldSelfRelation X x) :
    ∃ p : FieldValuedPoint X, Points.mk p = x ∧
      Etale (pullback.fst p.hom p.hom) ∧ QuasiCompact (pullback.fst p.hom p.hom) ∧
        Etale (pullback.snd p.hom p.hom) ∧ QuasiCompact (pullback.snd p.hom p.hom) :=
  sorry

end existsEtaleQuasiCompactFieldSelfRelation

/-- There is a monomorphism from the spectrum of a field in the equivalence class of
`x`. -/
def existsMonoFieldValuedPoint {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x

namespace existsMonoFieldValuedPoint

/-- A monomorphism `Spec(K) ⟶ X` in the class of `x` witnesses
`existsMonoFieldValuedPoint`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (p : FieldValuedPoint X) [Mono p.hom] (hx : Points.mk p = x) :
    existsMonoFieldValuedPoint X x :=
  sorry

/-- `existsMonoFieldValuedPoint X x` supplies a monomorphism from the spectrum of a field
in the class of `x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsMonoFieldValuedPoint X x) :
    ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x :=
  sorry

end existsMonoFieldValuedPoint

/-- Existence of an étale chart with finite self-relation fibre over `x` is equivalent to
existence of a monomorphism from the spectrum of a field in the class of `x`. -/
theorem existsEtaleRelationFiniteFibre_iff_existsMonoFieldValuedPoint
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    existsEtaleRelationFiniteFibre X x ↔ existsMonoFieldValuedPoint X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
