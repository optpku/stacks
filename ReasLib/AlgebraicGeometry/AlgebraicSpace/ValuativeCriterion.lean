/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.Valuation.Extension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Valuative criterion for morphisms of algebraic spaces

A morphism of algebraic spaces satisfies the uniqueness part of the valuative
criterion when every solid valuative square has at most one lift, the existence
part when every such square admits a dominating extension of valuation rings
together with a lift of the extended square, and the valuative criterion when
both parts hold.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

set_option backward.privateInPublic true in
/-- A valuative commutative square over a morphism `f : X ⟶ Y` of algebraic
spaces over `S` is a solid diagram `Spec(K) ⟶ X`, `Spec(R) ⟶ Y` with vertical
arrow `Spec(K) ⟶ Spec(R)`, where `R` is a valuation ring and `K` is a field of
fractions of `R`. -/
private structure ValuativeCommSqObj {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) where
  /-- The valuation ring of a valuative commutative square. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  /-- The field of fractions of a valuative commutative square. -/
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  /-- The structure morphism of `Spec(R)` over `S`. -/
  structureHom : Spec (.of R) ⟶ S
  /-- The top map `Spec(K) ⟶ X` of algebraic spaces over `S`. -/
  i₁ : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶ X
  /-- The bottom map `Spec(R) ⟶ Y` of algebraic spaces over `S`. -/
  i₂ : ofOver (Over.mk structureHom) ⟶ Y
  /-- The solid square commutes. -/
  commSq : CommSq i₁ (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl) f i₂

set_option backward.privateInPublic true in
/-- The object over the arrow `f` determined by a solid valuative square. -/
private def ValuativeCommSqObj.over {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (sq : ValuativeCommSqObj f) : Over (Arrow.mk f) :=
  Over.mk (Arrow.homMk' sq.i₁ sq.i₂ sq.commSq.w)

set_option backward.privateInPublic true in
/-- Valuative squares with morphisms induced from the slice over the arrow `f`. -/
abbrev ValuativeCommSq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :=
  InducedCategory (Over (Arrow.mk f)) (ValuativeCommSqObj.over (f := f))

namespace ValuativeCommSq

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

set_option backward.privateInPublic true in
/-- The valuation-ring carrier of a valuative square. -/
abbrev R (sq : ValuativeCommSq f) : Type u := ValuativeCommSqObj.R sq

set_option backward.privateInPublic true in
/-- The commutative ring structure of the valuation ring. -/
abbrev commRing (sq : ValuativeCommSq f) : CommRing sq.R := ValuativeCommSqObj.commRing sq

attribute [instance] commRing

set_option backward.privateInPublic true in
/-- The domain structure of the valuation ring. -/
abbrev domain (sq : ValuativeCommSq f) : IsDomain sq.R := ValuativeCommSqObj.domain sq

attribute [instance] domain

set_option backward.privateInPublic true in
/-- The valuation-ring structure stored in a valuative square. -/
abbrev valuationRing (sq : ValuativeCommSq f) : ValuationRing sq.R := ValuativeCommSqObj.valuationRing sq

attribute [instance] valuationRing

set_option backward.privateInPublic true in
/-- The fraction-field carrier of a valuative square. -/
abbrev K (sq : ValuativeCommSq f) : Type u := ValuativeCommSqObj.K sq

set_option backward.privateInPublic true in
/-- The field structure of the fraction field. -/
abbrev field (sq : ValuativeCommSq f) : Field sq.K := ValuativeCommSqObj.field sq

attribute [instance] field

set_option backward.privateInPublic true in
/-- The algebra structure of the fraction field over the valuation ring. -/
abbrev algebra (sq : ValuativeCommSq f) : Algebra sq.R sq.K := ValuativeCommSqObj.algebra sq

attribute [instance] algebra

set_option backward.privateInPublic true in
/-- The fraction-field property stored in a valuative square. -/
abbrev isFractionRing (sq : ValuativeCommSq f) : IsFractionRing sq.R sq.K := ValuativeCommSqObj.isFractionRing sq

attribute [instance] isFractionRing

set_option backward.privateInPublic true in
/-- The structure morphism of the valuation-ring spectrum. -/
abbrev structureHom (sq : ValuativeCommSq f) : Spec (.of sq.R) ⟶ S := ValuativeCommSqObj.structureHom sq

set_option backward.privateInPublic true in
/-- The generic arrow of a valuative square. -/
abbrev i₁ (sq : ValuativeCommSq f) : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom)) ⟶ X := ValuativeCommSqObj.i₁ sq

set_option backward.privateInPublic true in
/-- The valuation-ring arrow of a valuative square. -/
abbrev i₂ (sq : ValuativeCommSq f) : ofOver (Over.mk sq.structureHom) ⟶ Y := ValuativeCommSqObj.i₂ sq

set_option backward.privateInPublic true in
/-- The commutativity certificate of the solid valuative square. -/
abbrev commSq (sq : ValuativeCommSq f) : CommSq sq.i₁ (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl) f sq.i₂ := ValuativeCommSqObj.commSq sq

set_option backward.privateInPublic true in
/-- The slice object over `f` determined by a valuative square. -/
def over (sq : ValuativeCommSq f) : Over (Arrow.mk f) := ValuativeCommSqObj.over sq

/-- The induced forgetful functor from valuative squares to the slice over `f`. -/
def toOver (f : X ⟶ Y) : ValuativeCommSq f ⥤ Over (Arrow.mk f) :=
  inducedFunctor ValuativeCommSq.over

/-- The forgetful functor from valuative squares to the slice over `f` is fully faithful. -/
def toOverFullyFaithful (f : X ⟶ Y) : (toOver f).FullyFaithful :=
  fullyFaithfulInducedFunctor ValuativeCommSq.over


set_option backward.privateInPublic true in
/-- Construct a valuative commutative square from a valuation ring, a field of
fractions, a structure morphism over `S`, and the two solid arrows. -/
def of (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₁ : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶ X)
    (i₂ : ofOver (Over.mk structureHom) ⟶ Y)
    (commSq : CommSq i₁ (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl) f i₂) :
    ValuativeCommSq f where
  R := R
  K := K
  structureHom := structureHom
  i₁ := i₁
  i₂ := i₂
  commSq := commSq

/-- `Spec(R)` as a scheme over `S`. -/
abbrev specR (sq : ValuativeCommSq f) : Over S := Over.mk sq.structureHom

/-- `Spec(K)` as a scheme over `S`, via the algebra map `R → K`. -/
abbrev specK (sq : ValuativeCommSq f) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom)

/-- The vertical morphism `Spec(K) ⟶ Spec(R)` of algebraic spaces over `S`. -/
abbrev verticalMap (sq : ValuativeCommSq f) : ofOver sq.specK ⟶ ofOver sq.specR :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl

/-- The vertical arrow is `ofOverHomMk` of `Spec.map` of the algebra map. -/
theorem verticalMap_eq (sq : ValuativeCommSq f) :
    sq.verticalMap = ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl :=
  sorry

/-- The two paths `Spec(K) ⟶ Y` of a solid valuative square agree. -/
theorem spec (sq : ValuativeCommSq f) : sq.i₁ ≫ f = sq.verticalMap ≫ sq.i₂ := sorry

/-- The structure morphism of `ValuativeCommSq.of` is the given morphism to `S`. -/
theorem of_structureHom (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u)
    [Field K] [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₁ : ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶ X)
    (i₂ : ofOver (Over.mk structureHom) ⟶ Y)
    (commSq : CommSq i₁ (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl) f i₂) :
    (of R K structureHom i₁ i₂ commSq).structureHom = structureHom :=
  sorry

set_option backward.privateInPublic true in
/-- An extension of a valuative commutative square is a field extension `K'/K`,
a valuation ring `R'` of `K'` dominating `R`, and a morphism `Spec(R') ⟶ X`
filling the extended diagram. -/
private structure ExtensionObj (sq : ValuativeCommSq f) where
  /-- The dominating valuation ring. -/
  R' : Type u
  [commRing : CommRing R']
  [domain : IsDomain R']
  [valuationRing : ValuationRing R']
  /-- The extended field of fractions. -/
  K' : Type u
  [field : Field K']
  [algebra_R : Algebra sq.R R']
  [algebra_K : Algebra sq.K K']
  [algebra : Algebra R' K']
  [algebra_base : Algebra sq.R K']
  [isFractionRing : IsFractionRing R' K']
  [isExtension : IsExtensionOfValuationRings sq.R R']
  [isScalarTower_K : IsScalarTower sq.R sq.K K']
  [isScalarTower_R' : IsScalarTower sq.R R' K']
  /-- The two structure morphisms of `Spec(K')` over `S` agree. -/
  specK_compat :
    Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom
  /-- The outer solid square after extending the valuation ring commutes. -/
  outerCommSq :
    CommSq
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K'))) specK_compat ≫ sq.i₁)
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl) f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl ≫ sq.i₂)
  /-- A lift `Spec(R') ⟶ X` of the extended square. -/
  lift : outerCommSq.LiftStruct

set_option backward.privateInPublic true in
/-- The object over `X` determined by the lift of a dominating extension. -/
private def ExtensionObj.over {sq : ValuativeCommSq f} (e : ExtensionObj sq) : Over X :=
  Over.mk e.lift.l

set_option backward.privateInPublic true in
/-- Dominating extensions with lifts, with morphisms induced from the slice over `X`. -/
abbrev Extension (sq : ValuativeCommSq f) :=
  InducedCategory (Over X) (ExtensionObj.over (sq := sq))

namespace Extension

set_option backward.privateInPublic true in
/-- The dominating valuation-ring carrier. -/
abbrev R' {sq : ValuativeCommSq f} (e : Extension sq) :
    Type u := ExtensionObj.R' e

set_option backward.privateInPublic true in
/-- The commutative ring structure of the dominating valuation ring. -/
abbrev commRing {sq : ValuativeCommSq f} (e : Extension sq) :
    CommRing e.R' := ExtensionObj.commRing e

attribute [instance] commRing

set_option backward.privateInPublic true in
/-- The domain structure of the dominating valuation ring. -/
abbrev domain {sq : ValuativeCommSq f} (e : Extension sq) :
    IsDomain e.R' := ExtensionObj.domain e

attribute [instance] domain

set_option backward.privateInPublic true in
/-- The valuation-ring structure of the dominating ring. -/
abbrev valuationRing {sq : ValuativeCommSq f} (e : Extension sq) :
    ValuationRing e.R' := ExtensionObj.valuationRing e

attribute [instance] valuationRing

set_option backward.privateInPublic true in
/-- The extended fraction-field carrier. -/
abbrev K' {sq : ValuativeCommSq f} (e : Extension sq) :
    Type u := ExtensionObj.K' e

set_option backward.privateInPublic true in
/-- The field structure of the extended fraction field. -/
abbrev field {sq : ValuativeCommSq f} (e : Extension sq) :
    Field e.K' := ExtensionObj.field e

attribute [instance] field

set_option backward.privateInPublic true in
/-- The algebra structure of the dominating valuation ring over the original ring. -/
abbrev algebra_R {sq : ValuativeCommSq f} (e : Extension sq) :
    Algebra sq.R e.R' := ExtensionObj.algebra_R e

attribute [instance] algebra_R

set_option backward.privateInPublic true in
/-- The algebra structure of the extended field over the original field. -/
abbrev algebra_K {sq : ValuativeCommSq f} (e : Extension sq) :
    Algebra sq.K e.K' := ExtensionObj.algebra_K e

attribute [instance] algebra_K

set_option backward.privateInPublic true in
/-- The algebra structure of the extended field over the dominating ring. -/
abbrev algebra {sq : ValuativeCommSq f} (e : Extension sq) :
    Algebra e.R' e.K' := ExtensionObj.algebra e

attribute [instance] algebra

set_option backward.privateInPublic true in
/-- The algebra structure of the extended field over the original valuation ring. -/
abbrev algebra_base {sq : ValuativeCommSq f} (e : Extension sq) :
    Algebra sq.R e.K' := ExtensionObj.algebra_base e

attribute [instance] algebra_base

set_option backward.privateInPublic true in
/-- The fraction-field property of the extended field. -/
abbrev isFractionRing {sq : ValuativeCommSq f} (e : Extension sq) :
    IsFractionRing e.R' e.K' := ExtensionObj.isFractionRing e

attribute [instance] isFractionRing

set_option backward.privateInPublic true in
/-- The domination of the original valuation ring. -/
abbrev isExtension {sq : ValuativeCommSq f} (e : Extension sq) :
    IsExtensionOfValuationRings sq.R e.R' := ExtensionObj.isExtension e

attribute [instance] isExtension

set_option backward.privateInPublic true in
/-- Compatibility of scalar multiplication through the original fraction field. -/
abbrev isScalarTower_K {sq : ValuativeCommSq f} (e : Extension sq) :
    IsScalarTower sq.R sq.K e.K' := ExtensionObj.isScalarTower_K e

attribute [instance] isScalarTower_K

set_option backward.privateInPublic true in
/-- Compatibility of scalar multiplication through the dominating valuation ring. -/
abbrev isScalarTower_R' {sq : ValuativeCommSq f} (e : Extension sq) :
    IsScalarTower sq.R e.R' e.K' := ExtensionObj.isScalarTower_R' e

attribute [instance] isScalarTower_R'

set_option backward.privateInPublic true in
/-- Equality of the two structure morphisms from the extended field spectrum. -/
abbrev specK_compat {sq : ValuativeCommSq f} (e : Extension sq) :
    Spec.map (CommRingCat.ofHom (algebraMap sq.K e.K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
      Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom := ExtensionObj.specK_compat e

set_option backward.privateInPublic true in
/-- Commutativity of the extended solid square. -/
abbrev outerCommSq {sq : ValuativeCommSq f} (e : Extension sq) :
    CommSq
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K e.K'))) e.specK_compat ≫ sq.i₁)
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K'))) rfl) f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R'))) rfl ≫ sq.i₂) := ExtensionObj.outerCommSq e

set_option backward.privateInPublic true in
/-- The stored lift of the extended solid square. -/
abbrev lift {sq : ValuativeCommSq f} (e : Extension sq) :
    e.outerCommSq.LiftStruct := ExtensionObj.lift e

set_option backward.privateInPublic true in
/-- The slice object over `X` determined by an extended lift. -/
def over {sq : ValuativeCommSq f} (e : Extension sq) : Over X := ExtensionObj.over e

/-- The induced forgetful functor from dominating extensions with lifts to the slice over `X`. -/
def toOver (sq : ValuativeCommSq f) : Extension sq ⥤ Over X :=
  inducedFunctor Extension.over

/-- The forgetful functor from dominating extensions with lifts is fully faithful. -/
def toOverFullyFaithful (sq : ValuativeCommSq f) : (toOver sq).FullyFaithful :=
  fullyFaithfulInducedFunctor Extension.over

/-- The two structure morphisms `Spec(K') ⟶ S` obtained via `K` and via `R'` agree. -/
theorem specK_compat_of (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K'] :
    Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom :=
  sorry

set_option backward.privateInPublic true in
/-- Construct an extension of a valuative square from dominating valuation-ring
data and a morphism `Spec(R') ⟶ X` making both triangles of the extended
diagram commute. -/
def of (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R'] [ValuationRing R']
    (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K'] [Algebra R' K']
    [Algebra sq.R K'] [IsFractionRing R' K'] [IsExtensionOfValuationRings sq.R R']
    [IsScalarTower sq.R sq.K K'] [IsScalarTower sq.R R' K']
    (liftHom :
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom)) ⟶ X)
    (fac_left :
      ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl ≫ liftHom =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K')))
          (specK_compat_of sq R' K') ≫ sq.i₁)
    (fac_right :
      liftHom ≫ f =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl ≫ sq.i₂) :
    Extension sq where
  R' := R'
  K' := K'
  specK_compat := specK_compat_of sq R' K'
  outerCommSq := sorry
  lift := { l := liftHom, fac_left := fac_left, fac_right := fac_right }

/-- `Spec(R')` as a scheme over `S`, via the algebra map `R → R'`. -/
abbrev specR' {sq : ValuativeCommSq f} (e : Extension sq) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom)

/-- `Spec(K')` as a scheme over `S`, via the algebra map `R' → K'`. -/
abbrev specK' {sq : ValuativeCommSq f} (e : Extension sq) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
    Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom)

/-- The morphism `Spec(R') ⟶ Spec(R)` of algebraic spaces over `S`. -/
abbrev toSpecR {sq : ValuativeCommSq f} (e : Extension sq) :
    ofOver e.specR' ⟶ ofOver sq.specR :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R'))) rfl

/-- The morphism `Spec(K') ⟶ Spec(K)` of algebraic spaces over `S`. -/
abbrev toSpecK {sq : ValuativeCommSq f} (e : Extension sq) :
    ofOver e.specK' ⟶ ofOver sq.specK :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K e.K'))) e.specK_compat

/-- The vertical morphism `Spec(K') ⟶ Spec(R')` of algebraic spaces over `S`. -/
abbrev verticalMap {sq : ValuativeCommSq f} (e : Extension sq) :
    ofOver e.specK' ⟶ ofOver e.specR' :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K'))) rfl

/-- The morphism `Spec(R') ⟶ X` filling the extended valuative diagram. -/
def liftHom {sq : ValuativeCommSq f} (e : Extension sq) : ofOver e.specR' ⟶ X :=
  e.lift.l

/-- The morphism of `Extension.of` is the given lift `Spec(R') ⟶ X`. -/
theorem of_liftHom (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (liftHom :
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom)) ⟶ X)
    (fac_left :
      ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl ≫ liftHom =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K')))
          (specK_compat_of sq R' K') ≫ sq.i₁)
    (fac_right :
      liftHom ≫ f =
        ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl ≫ sq.i₂) :
    (of sq R' K' liftHom fac_left fac_right).liftHom = liftHom :=
  sorry

/-- The upper triangle of an extended valuative square commutes:
`Spec(K') ⟶ Spec(R') ⟶ X` equals `Spec(K') ⟶ Spec(K) ⟶ X`. -/
theorem fac_left {sq : ValuativeCommSq f} (e : Extension sq) :
    e.verticalMap ≫ e.liftHom = e.toSpecK ≫ sq.i₁ :=
  sorry

/-- The lower triangle of an extended valuative square commutes:
`Spec(R') ⟶ X ⟶ Y` equals `Spec(R') ⟶ Spec(R) ⟶ Y`. -/
theorem fac_right {sq : ValuativeCommSq f} (e : Extension sq) :
    e.liftHom ≫ f = e.toSpecR ≫ sq.i₂ :=
  sorry

end Extension

end ValuativeCommSq

/-- A morphism of algebraic spaces satisfies the uniqueness part of the valuative
criterion if every valuative commutative square has at most one lift. -/
@[mk_iff]
class ValuativeCriterion.Uniqueness {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every valuative square has at most one dotted lift. -/
  subsingleton_liftStruct : ∀ sq : ValuativeCommSq f, Subsingleton sq.commSq.LiftStruct

/-- A morphism of algebraic spaces satisfies the existence part of the valuative
criterion if every valuative commutative square admits a dominating extension
together with a lift of the extended square. -/
@[mk_iff]
class ValuativeCriterion.Existence {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every valuative square admits a dominating extension with a lift. -/
  nonempty_extension : ∀ sq : ValuativeCommSq f, Nonempty sq.Extension

/-- A morphism of algebraic spaces satisfies the valuative criterion if it
satisfies both the uniqueness and existence parts. -/
@[mk_iff]
class ValuativeCriterion {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop
    extends ValuativeCriterion.Uniqueness f, ValuativeCriterion.Existence f

namespace ValuativeCriterion.Uniqueness

/-- The identity morphism of an algebraic space satisfies the uniqueness part of
the valuative criterion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Uniqueness (𝟙 X) := sorry

/-- A morphism satisfies uniqueness if and only if every valuative square has at
most one lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Uniqueness f ↔ ∀ sq : ValuativeCommSq f, Subsingleton sq.commSq.LiftStruct :=
  sorry

end ValuativeCriterion.Uniqueness

namespace ValuativeCriterion.Existence

/-- The identity morphism of an algebraic space satisfies the existence part of
the valuative criterion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Existence (𝟙 X) := sorry

/-- A morphism satisfies existence if and only if every valuative square admits a
dominating extension with a lift. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Existence f ↔ ∀ sq : ValuativeCommSq f, Nonempty sq.Extension :=
  sorry

end ValuativeCriterion.Existence

namespace ValuativeCriterion

/-- The identity morphism of an algebraic space satisfies the valuative
criterion. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : ValuativeCriterion (𝟙 X) := sorry

/-- A morphism satisfies the valuative criterion if and only if it satisfies both
the uniqueness and existence parts. -/
theorem iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ValuativeCriterion f ↔ Uniqueness f ∧ Existence f :=
  sorry

end ValuativeCriterion

end AlgebraicGeometry.AlgebraicSpace
