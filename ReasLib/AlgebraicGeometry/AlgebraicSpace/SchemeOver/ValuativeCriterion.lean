/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.Valuation.Extension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver

/-!
# Existence part of the valuative criterion for scheme presheaves

A functor `F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)` satisfies the existence part
of the valuative criterion when every solid valuative square admits a
dominating extension of valuation rings together with an `F`-point over the
extended valuation ring restricting to the given generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SchemeOver

/-- The morphism `Spec(K) ⟶ Spec(R)` in `Over S` induced by `algebraMap R K`. -/
def specAlgebraMapOver {S : Scheme.{u}} (R K : Type u) [CommRing R] [CommRing K]
    [Algebra R K] (structureHom : Spec (.of R) ⟶ S) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom) ⟶
      Over.mk structureHom :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl

/-- The morphism `Spec(K') ⟶ Spec(K)` in `Over S` induced by `algebraMap K K'`,
using compatibility of the two structure morphisms of `Spec(K')`. -/
def specExtendOver {S : Scheme.{u}} {R K R' K' : Type u} [CommRing R] [CommRing K]
    [Algebra R K] [CommRing R'] [CommRing K'] [Algebra R R'] [Algebra K K']
    [Algebra R' K'] (structureHom : Spec (.of R) ⟶ S)
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) :
    Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K K'))) specK_compat

set_option backward.privateInPublic true in
/-- A valuative commutative square over a functor
`F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)` is a solid diagram with vertical arrow
`Spec(K) ⟶ Spec(R)` over `B`, where `R` is a valuation ring, `K` is a field of
fractions of `R`, and the top of the square is an `F`-point over `Spec(K)`. -/
private structure ValuativeCommSqObj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) where
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
  /-- The bottom map `Spec(R) ⟶ B` of algebraic spaces over `S`. -/
  i₂ : ofOver (Over.mk structureHom) ⟶ B
  /-- The generic `F`-point over `Spec(K)`. -/
  point : F.obj (op (CostructuredArrow.mk
    ((ofOverFunctor S).map (specAlgebraMapOver R K structureHom) ≫ i₂)))

set_option backward.privateInPublic true in
/-- Construct a valuative square from a valuation ring, its fraction field,
the spectrum morphisms over the base, and a generic presheaf point. -/
private def ValuativeCommSqObj.of {S : Scheme.{u}} {B : AlgebraicSpace S}
    {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₂ : ofOver (Over.mk structureHom) ⟶ B)
    (point : F.obj (op (CostructuredArrow.mk
      ((ofOverFunctor S).map (specAlgebraMapOver R K structureHom) ≫ i₂)))) :
    ValuativeCommSqObj F where
  R := R
  commRing := inferInstance
  domain := inferInstance
  valuationRing := inferInstance
  K := K
  field := inferInstance
  algebra := inferInstance
  isFractionRing := inferInstance
  structureHom := structureHom
  i₂ := i₂
  point := point

set_option backward.privateInPublic true in
/-- A valuation ring, its fraction field, a morphism from its spectrum to `B`,
and a generic point of the presheaf `F`. -/
abbrev ValuativeCommSq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) := ValuativeCommSqObj F

namespace ValuativeCommSq

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}

set_option backward.privateInPublic true in
/-- The valuation-ring carrier of a valuative square. -/
abbrev R (sq : ValuativeCommSq F) :
    Type u := ValuativeCommSqObj.R sq

set_option backward.privateInPublic true in
/-- The commutative ring structure of the valuation ring. -/
abbrev commRing (sq : ValuativeCommSq F) :
    CommRing sq.R := ValuativeCommSqObj.commRing sq

attribute [instance] commRing

set_option backward.privateInPublic true in
/-- The domain structure of the valuation ring. -/
abbrev domain (sq : ValuativeCommSq F) :
    IsDomain sq.R := ValuativeCommSqObj.domain sq

attribute [instance] domain

set_option backward.privateInPublic true in
/-- The valuation-ring structure of the test ring. -/
abbrev valuationRing (sq : ValuativeCommSq F) :
    ValuationRing sq.R := ValuativeCommSqObj.valuationRing sq

attribute [instance] valuationRing

set_option backward.privateInPublic true in
/-- The fraction-field carrier of a valuative square. -/
abbrev K (sq : ValuativeCommSq F) :
    Type u := ValuativeCommSqObj.K sq

set_option backward.privateInPublic true in
/-- The field structure of the fraction field. -/
abbrev field (sq : ValuativeCommSq F) :
    Field sq.K := ValuativeCommSqObj.field sq

attribute [instance] field

set_option backward.privateInPublic true in
/-- The algebra structure of the fraction field over the test ring. -/
abbrev algebra (sq : ValuativeCommSq F) :
    Algebra sq.R sq.K := ValuativeCommSqObj.algebra sq

attribute [instance] algebra

set_option backward.privateInPublic true in
/-- The fraction-field property of the generic field. -/
abbrev isFractionRing (sq : ValuativeCommSq F) :
    IsFractionRing sq.R sq.K := ValuativeCommSqObj.isFractionRing sq

attribute [instance] isFractionRing

set_option backward.privateInPublic true in
/-- The structure morphism of the valuation-ring spectrum over `S`. -/
abbrev structureHom (sq : ValuativeCommSq F) :
    Spec (.of sq.R) ⟶ S := ValuativeCommSqObj.structureHom sq

set_option backward.privateInPublic true in
/-- The morphism from the valuation-ring spectrum to `B`. -/
abbrev i₂ (sq : ValuativeCommSq F) :
    ofOver (Over.mk sq.structureHom) ⟶ B := ValuativeCommSqObj.i₂ sq

set_option backward.privateInPublic true in
/-- The generic point of the presheaf in a valuative square. -/
abbrev point (sq : ValuativeCommSq F) :
    F.obj (op (CostructuredArrow.mk
      ((ofOverFunctor S).map (specAlgebraMapOver sq.R sq.K sq.structureHom) ≫ sq.i₂))) := ValuativeCommSqObj.point sq

set_option backward.privateInPublic true in
/-- Construct a valuative commutative square from a valuation ring, a field of
fractions, a structure morphism over `S`, a morphism `Spec(R) ⟶ B`, and an
`F`-point over `Spec(K)`. -/
def of (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₂ : ofOver (Over.mk structureHom) ⟶ B)
    (point : F.obj (op (CostructuredArrow.mk
      ((ofOverFunctor S).map (specAlgebraMapOver R K structureHom) ≫ i₂)))) :
    ValuativeCommSq F :=
  ValuativeCommSqObj.of R K structureHom i₂ point

/-- `Spec(R)` as a scheme over `S`. -/
abbrev specR (sq : ValuativeCommSq F) : Over S := Over.mk sq.structureHom

/-- `Spec(K)` as a scheme over `S`, via the algebra map `R → K`. -/
abbrev specK (sq : ValuativeCommSq F) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom)

/-- The vertical morphism `Spec(K) ⟶ Spec(R)` of schemes over `S`. -/
abbrev verticalOver (sq : ValuativeCommSq F) : sq.specK ⟶ sq.specR :=
  specAlgebraMapOver sq.R sq.K sq.structureHom

/-- `Spec(R)` as a scheme over `B`. -/
abbrev schemesOverR (sq : ValuativeCommSq F) : SchemeOver B :=
  CostructuredArrow.mk
    (sq.i₂ : (ofOverFunctor S).obj (Over.mk sq.structureHom) ⟶ B)

/-- `Spec(K)` as a scheme over `B`, via the vertical algebra map. -/
abbrev schemesOverK (sq : ValuativeCommSq F) : SchemeOver B :=
  CostructuredArrow.mk ((ofOverFunctor S).map sq.verticalOver ≫ sq.i₂)

/-- The vertical morphism `Spec(K) ⟶ Spec(R)` of schemes over `B`. -/
abbrev verticalMap (sq : ValuativeCommSq F) : sq.schemesOverK ⟶ sq.schemesOverR :=
  CostructuredArrow.homMk sq.verticalOver rfl

/-- The generic point of `ValuativeCommSq.of` is the given `F`-point. -/
theorem of_point (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u)
    [Field K] [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₂ : ofOver (Over.mk structureHom) ⟶ B)
    (point : F.obj (op (CostructuredArrow.mk
      ((ofOverFunctor S).map (specAlgebraMapOver R K structureHom) ≫ i₂)))) :
    (of R K structureHom i₂ point).point = point := sorry

/-- The two structure morphisms `Spec(K') ⟶ S` obtained via `K` and via `R'`
agree. -/
theorem specK_compat_of (sq : ValuativeCommSq F) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K'] :
    Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom := sorry

/-- `Spec(R')` as a scheme over `B`, via the algebra map `R → R'`. -/
abbrev schemesOverR'Of (sq : ValuativeCommSq F) (R' : Type u) [CommRing R']
    [Algebra sq.R R'] : SchemeOver B :=
  CostructuredArrow.mk
    ((ofOverFunctor S).map (specAlgebraMapOver sq.R R' sq.structureHom) ≫ sq.i₂)

/-- `Spec(K')` as a scheme over `B`, via the algebra maps `R → R' → K'`. -/
abbrev schemesOverK'Of (sq : ValuativeCommSq F) (R' : Type u) [CommRing R']
    [Algebra sq.R R'] (K' : Type u) [CommRing K'] [Algebra R' K'] : SchemeOver B :=
  CostructuredArrow.mk
    ((ofOverFunctor S).map
        (specAlgebraMapOver R' K'
          (Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom)) ≫
      (ofOverFunctor S).map (specAlgebraMapOver sq.R R' sq.structureHom) ≫ sq.i₂)

/-- The vertical morphism `Spec(K') ⟶ Spec(R')` of schemes over `B`. -/
abbrev verticalMapOf (sq : ValuativeCommSq F) (R' : Type u) [CommRing R']
    [Algebra sq.R R'] (K' : Type u) [CommRing K'] [Algebra R' K'] :
    schemesOverK'Of sq R' K' ⟶ schemesOverR'Of sq R' :=
  CostructuredArrow.mkPrecomp
    ((ofOverFunctor S).map (specAlgebraMapOver sq.R R' sq.structureHom) ≫ sq.i₂)
    (specAlgebraMapOver R' K'
      (Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom))

/-- The triangle `Spec(K') ⟶ Spec(K) ⟶ B` agrees with `Spec(K') ⟶ Spec(R') ⟶ B`. -/
theorem toSpecKOf_w (sq : ValuativeCommSq F) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    (ofOverFunctor S).map (specExtendOver sq.structureHom specK_compat) ≫ sq.schemesOverK.hom =
      (schemesOverK'Of sq R' K').hom := sorry

/-- The morphism `Spec(K') ⟶ Spec(K)` of schemes over `B`. -/
def toSpecKOf (sq : ValuativeCommSq F) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    schemesOverK'Of sq R' K' ⟶ sq.schemesOverK :=
  CostructuredArrow.homMk (specExtendOver sq.structureHom specK_compat)
    (toSpecKOf_w sq R' K' specK_compat)

set_option backward.privateInPublic true in
/-- An extension of a valuative commutative square is a field extension `K'/K`,
a valuation ring `R'` of `K'` dominating `R`, and an `F`-point over `Spec(R')`
restricting to the pullback of the given generic point along `Spec(K') ⟶ Spec(K)`. -/
private structure ExtensionObj (sq : ValuativeCommSq F) where
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
  /-- An `F`-point over `Spec(R')` filling the extended valuative diagram. -/
  lift : F.obj (op (schemesOverR'Of sq R'))
  /-- The lifted point restricts to the pullback of the generic point along
  `Spec(K') ⟶ Spec(K)`. -/
  fac :
    F.map (op (verticalMapOf sq R' K')) lift =
      F.map (op (toSpecKOf sq R' K' specK_compat)) sq.point

set_option backward.privateInPublic true in
/-- Construct a dominating extension of a valuative square from its valuation
ring and fraction field, compatible spectrum morphisms, and a lifted presheaf
point satisfying the generic-fibre restriction equation. -/
private def ExtensionObj.of (sq : ValuativeCommSq F)
    (R' : Type u) [CommRing R'] [IsDomain R'] [ValuationRing R']
    (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K'] [Algebra R' K']
    [Algebra sq.R K'] [IsFractionRing R' K'] [IsExtensionOfValuationRings sq.R R']
    [IsScalarTower sq.R sq.K K'] [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom)
    (lift : F.obj (op (schemesOverR'Of sq R')))
    (fac :
      F.map (op (verticalMapOf sq R' K')) lift =
        F.map (op (toSpecKOf sq R' K' specK_compat)) sq.point) :
    ExtensionObj sq where
  R' := R'
  commRing := inferInstance
  domain := inferInstance
  valuationRing := inferInstance
  K' := K'
  field := inferInstance
  algebra_R := inferInstance
  algebra_K := inferInstance
  algebra := inferInstance
  algebra_base := inferInstance
  isFractionRing := inferInstance
  isExtension := inferInstance
  isScalarTower_K := inferInstance
  isScalarTower_R' := inferInstance
  specK_compat := specK_compat
  lift := lift
  fac := fac

set_option backward.privateInPublic true in
/-- A dominating extension of a valuative square together with a lifted
presheaf point and its generic-fibre restriction law. -/
abbrev Extension (sq : ValuativeCommSq F) := ExtensionObj sq

namespace Extension

set_option backward.privateInPublic true in
/-- The carrier of the dominating valuation ring. -/
abbrev R' {sq : ValuativeCommSq F} (e : Extension sq) :
    Type u := ExtensionObj.R' e

set_option backward.privateInPublic true in
/-- The commutative ring structure of the dominating ring. -/
abbrev commRing {sq : ValuativeCommSq F} (e : Extension sq) :
    CommRing e.R' := ExtensionObj.commRing e

attribute [instance] commRing

set_option backward.privateInPublic true in
/-- The domain structure of the dominating ring. -/
abbrev domain {sq : ValuativeCommSq F} (e : Extension sq) :
    IsDomain e.R' := ExtensionObj.domain e

attribute [instance] domain

set_option backward.privateInPublic true in
/-- The valuation-ring structure of the dominating ring. -/
abbrev valuationRing {sq : ValuativeCommSq F} (e : Extension sq) :
    ValuationRing e.R' := ExtensionObj.valuationRing e

attribute [instance] valuationRing

set_option backward.privateInPublic true in
/-- The carrier of the extended fraction field. -/
abbrev K' {sq : ValuativeCommSq F} (e : Extension sq) :
    Type u := ExtensionObj.K' e

set_option backward.privateInPublic true in
/-- The field structure of the extended fraction field. -/
abbrev field {sq : ValuativeCommSq F} (e : Extension sq) :
    Field e.K' := ExtensionObj.field e

attribute [instance] field

set_option backward.privateInPublic true in
/-- The algebra structure of the dominating ring over the test ring. -/
abbrev algebra_R {sq : ValuativeCommSq F} (e : Extension sq) :
    Algebra sq.R e.R' := ExtensionObj.algebra_R e

attribute [instance] algebra_R

set_option backward.privateInPublic true in
/-- The algebra structure of the extended field over the generic field. -/
abbrev algebra_K {sq : ValuativeCommSq F} (e : Extension sq) :
    Algebra sq.K e.K' := ExtensionObj.algebra_K e

attribute [instance] algebra_K

set_option backward.privateInPublic true in
/-- The algebra structure of the extended fraction field over its valuation ring. -/
abbrev algebra {sq : ValuativeCommSq F} (e : Extension sq) :
    Algebra e.R' e.K' := ExtensionObj.algebra e

attribute [instance] algebra

set_option backward.privateInPublic true in
/-- The algebra structure of the extended field over the original test ring. -/
abbrev algebra_base {sq : ValuativeCommSq F} (e : Extension sq) :
    Algebra sq.R e.K' := ExtensionObj.algebra_base e

attribute [instance] algebra_base

set_option backward.privateInPublic true in
/-- The fraction-field property of the extended field. -/
abbrev isFractionRing {sq : ValuativeCommSq F} (e : Extension sq) :
    IsFractionRing e.R' e.K' := ExtensionObj.isFractionRing e

attribute [instance] isFractionRing

set_option backward.privateInPublic true in
/-- The domination property of the valuation-ring extension. -/
abbrev isExtension {sq : ValuativeCommSq F} (e : Extension sq) :
    IsExtensionOfValuationRings sq.R e.R' := ExtensionObj.isExtension e

attribute [instance] isExtension

set_option backward.privateInPublic true in
/-- Compatibility of scalar multiplication through the original generic field. -/
abbrev isScalarTower_K {sq : ValuativeCommSq F} (e : Extension sq) :
    IsScalarTower sq.R sq.K e.K' := ExtensionObj.isScalarTower_K e

attribute [instance] isScalarTower_K

set_option backward.privateInPublic true in
/-- Compatibility of scalar multiplication through the dominating valuation ring. -/
abbrev isScalarTower_R' {sq : ValuativeCommSq F} (e : Extension sq) :
    IsScalarTower sq.R e.R' e.K' := ExtensionObj.isScalarTower_R' e

attribute [instance] isScalarTower_R'

set_option backward.privateInPublic true in
/-- The two structure morphisms from the extended generic spectrum agree. -/
abbrev specK_compat {sq : ValuativeCommSq F} (e : Extension sq) :
    Spec.map (CommRingCat.ofHom (algebraMap sq.K e.K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
      Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom := ExtensionObj.specK_compat e

set_option backward.privateInPublic true in
/-- The presheaf point over the dominating valuation ring. -/
abbrev lift {sq : ValuativeCommSq F} (e : Extension sq) :
    F.obj (op (schemesOverR'Of sq e.R')) := ExtensionObj.lift e

set_option backward.privateInPublic true in
/-- The lifted point restricts to the pullback of the original generic point. -/
abbrev fac {sq : ValuativeCommSq F} (e : Extension sq) :
    F.map (op (verticalMapOf sq e.R' e.K')) e.lift =
      F.map (op (toSpecKOf sq e.R' e.K' e.specK_compat)) sq.point := ExtensionObj.fac e

set_option backward.privateInPublic true in
/-- Construct an extension of a valuative square from dominating valuation-ring
data and an `F`-point over `Spec(R')` compatible with the generic point. -/
def of (sq : ValuativeCommSq F) (R' : Type u) [CommRing R'] [IsDomain R'] [ValuationRing R']
    (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K'] [Algebra R' K']
    [Algebra sq.R K'] [IsFractionRing R' K'] [IsExtensionOfValuationRings sq.R R']
    [IsScalarTower sq.R sq.K K'] [IsScalarTower sq.R R' K']
    (lift : F.obj (op (schemesOverR'Of sq R')))
    (fac :
      F.map (op (verticalMapOf sq R' K')) lift =
        F.map (op (toSpecKOf sq R' K' (specK_compat_of sq R' K'))) sq.point) :
    Extension sq :=
  ExtensionObj.of sq R' K' (specK_compat_of sq R' K') lift fac

/-- `Spec(R')` as a scheme over `S`, via the algebra map `R → R'`. -/
abbrev specR' {sq : ValuativeCommSq F} (e : Extension sq) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom)

/-- `Spec(K')` as a scheme over `S`, via the algebra map `R' → K'`. -/
abbrev specK' {sq : ValuativeCommSq F} (e : Extension sq) : Over S :=
  Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
      Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom)

/-- `Spec(R')` as a scheme over `B`. -/
abbrev schemesOverR' {sq : ValuativeCommSq F} (e : Extension sq) : SchemeOver B :=
  schemesOverR'Of sq e.R'

/-- `Spec(K')` as a scheme over `B`. -/
abbrev schemesOverK' {sq : ValuativeCommSq F} (e : Extension sq) : SchemeOver B :=
  schemesOverK'Of sq e.R' e.K'

/-- The morphism `Spec(R') ⟶ Spec(R)` of schemes over `B`. -/
abbrev toSpecR {sq : ValuativeCommSq F} (e : Extension sq) :
    e.schemesOverR' ⟶ sq.schemesOverR :=
  CostructuredArrow.homMk (specAlgebraMapOver sq.R e.R' sq.structureHom) rfl

/-- The morphism `Spec(K') ⟶ Spec(K)` of schemes over `B`. -/
abbrev toSpecK {sq : ValuativeCommSq F} (e : Extension sq) :
    e.schemesOverK' ⟶ sq.schemesOverK :=
  toSpecKOf sq e.R' e.K' e.specK_compat

/-- The vertical morphism `Spec(K') ⟶ Spec(R')` of schemes over `B`. -/
abbrev verticalMap {sq : ValuativeCommSq F} (e : Extension sq) :
    e.schemesOverK' ⟶ e.schemesOverR' :=
  verticalMapOf sq e.R' e.K'

/-- The lifted `F`-point of `Extension.of` is the given point over `Spec(R')`. -/
theorem of_lift (sq : ValuativeCommSq F) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (lift : F.obj (op (schemesOverR'Of sq R')))
    (fac :
      F.map (op (verticalMapOf sq R' K')) lift =
        F.map (op (toSpecKOf sq R' K' (specK_compat_of sq R' K'))) sq.point) :
    (of sq R' K' lift fac).lift = lift := sorry

/-- The dominating ring map is injective and local, and the lifted point
restricts to the pullback of the original generic point. -/
theorem spec {sq : ValuativeCommSq F} (e : Extension sq) :
    Function.Injective (algebraMap sq.R e.R') ∧
      IsLocalHom (algebraMap sq.R e.R') ∧
      F.map (op e.verticalMap) e.lift = F.map (op e.toSpecK) sq.point := sorry

end Extension

end ValuativeCommSq

/-- A functor `F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)` satisfies the existence
part of the valuative criterion if every valuative commutative square admits a
dominating extension together with a lift of the generic `F`-point. -/
@[mk_iff]
class ValuativeCriterion.Existence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop where
  /-- Every valuative square admits a dominating extension with a lifted point. -/
  nonempty_extension : ∀ sq : ValuativeCommSq F, Nonempty sq.Extension

namespace ValuativeCriterion.Existence

/-- The constant functor at the terminal type satisfies the existence part of
the valuative criterion. -/
instance instConst {S : Scheme.{u}} {B : AlgebraicSpace S} :
    Existence ((Functor.const ((SchemeOver B)ᵒᵖ)).obj PUnit.{u + 2}) := sorry

/-- A functor satisfies existence if and only if every valuative square admits a
dominating extension with a lifted point. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    Existence F ↔ ∀ sq : ValuativeCommSq F, Nonempty sq.Extension := sorry

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicSpace.SchemeOver
