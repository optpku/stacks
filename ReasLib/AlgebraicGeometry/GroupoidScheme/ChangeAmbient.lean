module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupoidScheme

/-!
# Changing the ambient scheme of a groupoid scheme

This module retains the object and arrow schemes of a groupoid over a new ambient scheme
whenever the source and target maps have the same composite to that scheme.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The object scheme of a groupoid after retaining its objects over a new ambient base. -/
abbrev changeAmbientU {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) : Over S :=
  Over.mk q

/-- The arrow scheme of a groupoid after retaining its source map over a new ambient base. -/
abbrev changeAmbientR {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) : Over S :=
  Over.mk (H.s.left ≫ q)

/-- The retained source map over a new ambient base. -/
def changeAmbientSource {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) : changeAmbientR H q ⟶ changeAmbientU H q :=
  Over.homMk H.s.left

/-- The retained target map is a morphism over the new ambient base. -/
theorem changeAmbientTarget_condition {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    H.t.left ≫ q = (changeAmbientR H q).hom := sorry

/-- The retained target map over a new ambient base. -/
def changeAmbientTarget {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientR H q ⟶ changeAmbientU H q :=
  Over.homMk H.t.left (changeAmbientTarget_condition H q h)

/-- The underlying comparison between the two ambient-base presentations of composable arrows. -/
def changeAmbientComposable {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    (pullback (changeAmbientSource H q) (changeAmbientTarget H q h)).left ⟶
      (pullback H.s H.t).left :=
  (PreservesPullback.iso (Over.forget S) (changeAmbientSource H q)
      (changeAmbientTarget H q h)).hom ≫
    (PreservesPullback.iso (Over.forget T) H.s H.t).inv

/-- Retained composition respects the new ambient structure map. -/
theorem changeAmbientComposition_condition {S T : Scheme.{u}}
    (H : GroupoidScheme T) (q : H.U.left ⟶ S)
    (h : H.t.left ≫ q = H.s.left ≫ q) :
    (changeAmbientComposable H q h ≫ H.c.left) ≫ (changeAmbientR H q).hom =
      (pullback (changeAmbientSource H q) (changeAmbientTarget H q h)).hom := sorry

/-- The retained composition map over a new ambient base. -/
def changeAmbientComposition {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    pullback (changeAmbientSource H q) (changeAmbientTarget H q h) ⟶
      changeAmbientR H q :=
  Over.homMk (changeAmbientComposable H q h ≫ H.c.left)
    (changeAmbientComposition_condition H q h)

/-- Retained identity arrows respect the new ambient structure map. -/
theorem changeAmbientIdentity_condition {S T : Scheme.{u}}
    (H : GroupoidScheme T) (q : H.U.left ⟶ S) :
    H.e.left ≫ (changeAmbientR H q).hom = (changeAmbientU H q).hom := sorry

/-- The retained identity map over a new ambient base. -/
def changeAmbientIdentity {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) : changeAmbientU H q ⟶ changeAmbientR H q :=
  Over.homMk H.e.left (changeAmbientIdentity_condition H q)

/-- Retained inverse arrows respect the new ambient structure map. -/
theorem changeAmbientInverse_condition {S T : Scheme.{u}}
    (H : GroupoidScheme T) (q : H.U.left ⟶ S) :
    H.i.left ≫ (changeAmbientR H q).hom = (changeAmbientR H q).hom := sorry

/-- The retained inverse map over a new ambient base. -/
def changeAmbientInverse {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) : changeAmbientR H q ⟶ changeAmbientR H q :=
  Over.homMk H.i.left (changeAmbientInverse_condition H q)

/-- Retained composition has the source of its second arrow. -/
theorem changeAmbient_compSource {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientComposition H q h ≫ changeAmbientSource H q =
      pullback.snd (changeAmbientSource H q) (changeAmbientTarget H q h) ≫
        changeAmbientSource H q := sorry

/-- Retained composition has the target of its first arrow. -/
theorem changeAmbient_compTarget {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientComposition H q h ≫ changeAmbientTarget H q h =
      pullback.fst (changeAmbientSource H q) (changeAmbientTarget H q h) ≫
        changeAmbientTarget H q h := sorry

/-- Retained identity arrows have the specified source. -/
theorem changeAmbient_identitySource {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) :
    changeAmbientIdentity H q ≫ changeAmbientSource H q = 𝟙 (changeAmbientU H q) := sorry

/-- Retained identity arrows have the specified target. -/
theorem changeAmbient_identityTarget {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientIdentity H q ≫ changeAmbientTarget H q h = 𝟙 (changeAmbientU H q) := sorry

/-- Retained inversion exchanges source and target. -/
theorem changeAmbient_inverseSource {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientInverse H q ≫ changeAmbientSource H q = changeAmbientTarget H q h := sorry

/-- Retained inversion exchanges target and source. -/
theorem changeAmbient_inverseTarget {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    changeAmbientInverse H q ≫ changeAmbientTarget H q h = changeAmbientSource H q := sorry

/-- Retained composition is associative on points over the new ambient base. -/
theorem changeAmbient_associativity {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    ∀ {X : Over S} (a b d : X ⟶ changeAmbientR H q)
      (h_ab : a ≫ changeAmbientSource H q = b ≫ changeAmbientTarget H q h)
      (h_bd : b ≫ changeAmbientSource H q = d ≫ changeAmbientTarget H q h)
      (h_ab_d : (pullback.lift a b h_ab ≫ changeAmbientComposition H q h) ≫
        changeAmbientSource H q = d ≫ changeAmbientTarget H q h)
      (h_a_bd : a ≫ changeAmbientSource H q =
        (pullback.lift b d h_bd ≫ changeAmbientComposition H q h) ≫
          changeAmbientTarget H q h),
      pullback.lift (pullback.lift a b h_ab ≫ changeAmbientComposition H q h) d h_ab_d ≫
          changeAmbientComposition H q h =
        pullback.lift a (pullback.lift b d h_bd ≫ changeAmbientComposition H q h) h_a_bd ≫
          changeAmbientComposition H q h := sorry

/-- Retained composition has the right identity law. -/
theorem changeAmbient_rightIdentity {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    ∀ {X : Over S} (a : X ⟶ changeAmbientR H q)
      (ha : a ≫ changeAmbientSource H q =
        ((a ≫ changeAmbientSource H q) ≫ changeAmbientIdentity H q) ≫
          changeAmbientTarget H q h),
      pullback.lift a ((a ≫ changeAmbientSource H q) ≫ changeAmbientIdentity H q) ha ≫
        changeAmbientComposition H q h = a := sorry

/-- Retained composition has the left identity law. -/
theorem changeAmbient_leftIdentity {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    ∀ {X : Over S} (a : X ⟶ changeAmbientR H q)
      (ha : ((a ≫ changeAmbientTarget H q h) ≫ changeAmbientIdentity H q) ≫
          changeAmbientSource H q = a ≫ changeAmbientTarget H q h),
      pullback.lift ((a ≫ changeAmbientTarget H q h) ≫ changeAmbientIdentity H q) a ha ≫
        changeAmbientComposition H q h = a := sorry

/-- Retained composition of an arrow with its inverse is its target identity. -/
theorem changeAmbient_inverseComp {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    ∀ {X : Over S} (a : X ⟶ changeAmbientR H q)
      (ha : a ≫ changeAmbientSource H q =
        (a ≫ changeAmbientInverse H q) ≫ changeAmbientTarget H q h),
      pullback.lift a (a ≫ changeAmbientInverse H q) ha ≫
          changeAmbientComposition H q h =
        (a ≫ changeAmbientTarget H q h) ≫ changeAmbientIdentity H q := sorry

/-- Retained composition of an inverse with its arrow is its source identity. -/
theorem changeAmbient_compInverse {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) :
    ∀ {X : Over S} (a : X ⟶ changeAmbientR H q)
      (ha : (a ≫ changeAmbientInverse H q) ≫ changeAmbientSource H q =
        a ≫ changeAmbientTarget H q h),
      pullback.lift (a ≫ changeAmbientInverse H q) a ha ≫
          changeAmbientComposition H q h =
        (a ≫ changeAmbientSource H q) ≫ changeAmbientIdentity H q := sorry

/-- Retain a groupoid's object and arrow schemes over a new ambient base when source and target
have the same composite to that base. -/
def changeAmbient {S T : Scheme.{u}} (H : GroupoidScheme T)
    (q : H.U.left ⟶ S) (h : H.t.left ≫ q = H.s.left ≫ q) : GroupoidScheme S where
  U := changeAmbientU H q
  R := changeAmbientR H q
  s := changeAmbientSource H q
  t := changeAmbientTarget H q h
  c := changeAmbientComposition H q h
  e := changeAmbientIdentity H q
  i := changeAmbientInverse H q
  comp_source := changeAmbient_compSource H q h
  comp_target := changeAmbient_compTarget H q h
  identity_source := changeAmbient_identitySource H q
  identity_target := changeAmbient_identityTarget H q h
  inverse_source := changeAmbient_inverseSource H q h
  inverse_target := changeAmbient_inverseTarget H q h
  associativity := changeAmbient_associativity H q h
  right_identity := changeAmbient_rightIdentity H q h
  left_identity := changeAmbient_leftIdentity H q h
  inverse_comp := changeAmbient_inverseComp H q h
  comp_inverse := changeAmbient_compInverse H q h


end AlgebraicGeometry.GroupoidScheme
