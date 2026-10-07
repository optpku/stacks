module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.Valuation.Extension
public import stacks_project.Chap99.«99_7_1_1_Functor»

/-!
# Existence part of the valuative criterion at Quot size

A functor `F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)` satisfies the existence part
of the valuative criterion when every solid valuative square admits a
dominating extension of valuation rings together with an `F`-point over the
extended valuation ring restricting to the given generic point, matching
Definition 67.41.1 at the Hom-universe of `Quot.quot`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- The morphism `Spec(K) ⟶ Spec(R)` in `Over S` induced by `algebraMap R K`. -/
def specAlgebraMapOver {S : Scheme.{u}} (R K : Type u) [CommRing R] [CommRing K]
    [Algebra R K] (structureHom : Spec (.of R) ⟶ S) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom) ⟶
      Over.mk structureHom :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl

/-- `specAlgebraMapOver` is `Over.homMk` of `Spec.map` of the algebra map. -/
theorem specAlgebraMapOver_eq {S : Scheme.{u}} (R K : Type u) [CommRing R] [CommRing K]
    [Algebra R K] (structureHom : Spec (.of R) ⟶ S) :
    specAlgebraMapOver R K structureHom =
      Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl :=
  sorry

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

/-- `specExtendOver` is `Over.homMk` of `Spec.map` of the algebra map `K → K'`. -/
theorem specExtendOver_eq {S : Scheme.{u}} {R K R' K' : Type u} [CommRing R] [CommRing K]
    [Algebra R K] [CommRing R'] [CommRing K'] [Algebra R R'] [Algebra K K']
    [Algebra R' K'] (structureHom : Spec (.of R) ⟶ S)
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ structureHom) :
    specExtendOver structureHom specK_compat =
      Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K K'))) specK_compat :=
  sorry

/-- A valuative commutative square over a functor
`F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)` is a solid diagram with vertical arrow
`Spec(K) ⟶ Spec(R)` over `B`, where `R` is a valuation ring, `K` is a field of
fractions of `R`, and the top of the square is an `F`-point over `Spec(K)`. -/
structure ValuativeCommSq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)) where
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

namespace ValuativeCommSq

attribute [instance] commRing domain valuationRing field algebra isFractionRing

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)}

/-- Construct a valuative commutative square from a valuation ring, a field of
fractions, a structure morphism over `S`, a morphism `Spec(R) ⟶ B`, and an
`F`-point over `Spec(K)`. -/
def of (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₂ : ofOver (Over.mk structureHom) ⟶ B)
    (point : F.obj (op (CostructuredArrow.mk
      ((ofOverFunctor S).map (specAlgebraMapOver R K structureHom) ≫ i₂)))) :
    ValuativeCommSq F where
  R := R
  K := K
  structureHom := structureHom
  i₂ := i₂
  point := point

/-- `Spec(R)` as a scheme over `S`. -/
abbrev specR (sq : ValuativeCommSq F) : Over S := Over.mk sq.structureHom

/-- `Spec(K)` as a scheme over `S`, via the algebra map `R → K`. -/
abbrev specK (sq : ValuativeCommSq F) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom)

/-- The vertical morphism `Spec(K) ⟶ Spec(R)` of schemes over `S`. -/
abbrev verticalOver (sq : ValuativeCommSq F) : sq.specK ⟶ sq.specR :=
  specAlgebraMapOver sq.R sq.K sq.structureHom

/-- `Spec(R)` as a scheme over `B`. -/
abbrev schemesOverR (sq : ValuativeCommSq F) : SchemesOver B :=
  CostructuredArrow.mk
    (sq.i₂ : (ofOverFunctor S).obj (Over.mk sq.structureHom) ⟶ B)

/-- `Spec(K)` as a scheme over `B`, via the vertical algebra map. -/
abbrev schemesOverK (sq : ValuativeCommSq F) : SchemesOver B :=
  CostructuredArrow.mk ((ofOverFunctor S).map sq.verticalOver ≫ sq.i₂)

/-- The vertical morphism `Spec(K) ⟶ Spec(R)` of schemes over `B`. -/
abbrev verticalMap (sq : ValuativeCommSq F) : sq.schemesOverK ⟶ sq.schemesOverR :=
  CostructuredArrow.homMk sq.verticalOver rfl

/-- The structure morphism of `ValuativeCommSq.of` is the given morphism to `S`. -/
theorem of_structureHom (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u)
    [Field K] [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₂ : ofOver (Over.mk structureHom) ⟶ B)
    (point : F.obj (op (CostructuredArrow.mk
      ((ofOverFunctor S).map (specAlgebraMapOver R K structureHom) ≫ i₂)))) :
    (of R K structureHom i₂ point).structureHom = structureHom :=
  sorry

/-- The generic point of `ValuativeCommSq.of` is the given `F`-point. -/
theorem of_point (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u)
    [Field K] [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₂ : ofOver (Over.mk structureHom) ⟶ B)
    (point : F.obj (op (CostructuredArrow.mk
      ((ofOverFunctor S).map (specAlgebraMapOver R K structureHom) ≫ i₂)))) :
    (of R K structureHom i₂ point).point = point :=
  sorry

/-- `specR` is `Over.mk` of the structure morphism of `Spec(R)`. -/
theorem specR_eq (sq : ValuativeCommSq F) : sq.specR = Over.mk sq.structureHom :=
  sorry

/-- `specK` is `Over.mk` of the structure morphism of `Spec(K)`. -/
theorem specK_eq (sq : ValuativeCommSq F) :
    sq.specK =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom) :=
  sorry

/-- `schemesOverR` is `CostructuredArrow.mk` of the morphism `Spec(R) ⟶ B`. -/
theorem schemesOverR_eq (sq : ValuativeCommSq F) :
    sq.schemesOverR =
      CostructuredArrow.mk
        (sq.i₂ : (ofOverFunctor S).obj (Over.mk sq.structureHom) ⟶ B) :=
  sorry

/-- `schemesOverK` is `CostructuredArrow.mk` of the composite `Spec(K) ⟶ Spec(R) ⟶ B`. -/
theorem schemesOverK_eq (sq : ValuativeCommSq F) :
    sq.schemesOverK = CostructuredArrow.mk ((ofOverFunctor S).map sq.verticalOver ≫ sq.i₂) :=
  sorry

/-- The vertical arrow of schemes over `B` is `mkPrecomp` of the algebra map. -/
theorem verticalMap_eq (sq : ValuativeCommSq F) :
    sq.verticalMap = CostructuredArrow.homMk sq.verticalOver rfl :=
  sorry

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
        Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom :=
  sorry

/-- `Spec(R')` as a scheme over `B`, via the algebra map `R → R'`. -/
abbrev schemesOverR'Of (sq : ValuativeCommSq F) (R' : Type u) [CommRing R']
    [Algebra sq.R R'] : SchemesOver B :=
  CostructuredArrow.mk
    ((ofOverFunctor S).map (specAlgebraMapOver sq.R R' sq.structureHom) ≫ sq.i₂)

/-- `Spec(K')` as a scheme over `B`, via the algebra maps `R → R' → K'`. -/
abbrev schemesOverK'Of (sq : ValuativeCommSq F) (R' : Type u) [CommRing R']
    [Algebra sq.R R'] (K' : Type u) [CommRing K'] [Algebra R' K'] : SchemesOver B :=
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
theorem toSpecK_w_of (sq : ValuativeCommSq F) (R' : Type u) [CommRing R'] [IsDomain R']
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
      (schemesOverK'Of sq R' K').hom :=
  sorry

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
    (toSpecK_w_of sq R' K' specK_compat)

/-- `schemesOverR'Of` is `CostructuredArrow.mk` of `Spec(R') ⟶ Spec(R) ⟶ B`. -/
theorem schemesOverR'Of_eq (sq : ValuativeCommSq F) (R' : Type u) [CommRing R']
    [Algebra sq.R R'] :
    schemesOverR'Of sq R' =
      CostructuredArrow.mk
        ((ofOverFunctor S).map (specAlgebraMapOver sq.R R' sq.structureHom) ≫ sq.i₂) :=
  sorry

/-- `toSpecKOf` is `CostructuredArrow.homMk` of `specExtendOver`. -/
theorem toSpecKOf_eq (sq : ValuativeCommSq F) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    toSpecKOf sq R' K' specK_compat =
      CostructuredArrow.homMk (specExtendOver sq.structureHom specK_compat)
        (toSpecK_w_of sq R' K' specK_compat) :=
  sorry

/-- An extension of a valuative commutative square is a field extension `K'/K`,
a valuation ring `R'` of `K'` dominating `R`, and an `F`-point over `Spec(R')`
restricting to the pullback of the given generic point along `Spec(K') ⟶ Spec(K)`. -/
structure Extension (sq : ValuativeCommSq F) where
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

namespace Extension

attribute [instance] commRing domain valuationRing field algebra_R algebra_K algebra algebra_base
  isFractionRing isExtension isScalarTower_K isScalarTower_R'

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
    Extension sq where
  R' := R'
  K' := K'
  specK_compat := specK_compat_of sq R' K'
  lift := lift
  fac := fac

/-- `Spec(R')` as a scheme over `S`, via the algebra map `R → R'`. -/
abbrev specR' {sq : ValuativeCommSq F} (e : Extension sq) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom)

/-- `Spec(K')` as a scheme over `S`, via the algebra map `R' → K'`. -/
abbrev specK' {sq : ValuativeCommSq F} (e : Extension sq) : Over S :=
  Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
      Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom)

/-- `Spec(R')` as a scheme over `B`. -/
abbrev schemesOverR' {sq : ValuativeCommSq F} (e : Extension sq) : SchemesOver B :=
  schemesOverR'Of sq e.R'

/-- `Spec(K')` as a scheme over `B`. -/
abbrev schemesOverK' {sq : ValuativeCommSq F} (e : Extension sq) : SchemesOver B :=
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
    (of sq R' K' lift fac).lift = lift :=
  sorry

/-- The restriction of the lifted point along `Spec(K') ⟶ Spec(R')` equals the
pullback of the generic point along `Spec(K') ⟶ Spec(K)`. -/
theorem fac_eq {sq : ValuativeCommSq F} (e : Extension sq) :
    F.map (op e.verticalMap) e.lift = F.map (op e.toSpecK) sq.point :=
  sorry

/-- `schemesOverR'` is `schemesOverR'Of` of the dominating valuation ring. -/
theorem schemesOverR'_eq {sq : ValuativeCommSq F} (e : Extension sq) :
    e.schemesOverR' = schemesOverR'Of sq e.R' :=
  sorry

/-- `toSpecK` is `toSpecKOf` of the stored compatibility of structure morphisms. -/
theorem toSpecK_eq {sq : ValuativeCommSq F} (e : Extension sq) :
    e.toSpecK = toSpecKOf sq e.R' e.K' e.specK_compat :=
  sorry

end Extension

end ValuativeCommSq

/-- A functor `F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)` satisfies the existence
part of the valuative criterion if every valuative commutative square admits a
dominating extension together with a lift of the generic `F`-point. -/
@[mk_iff]
class ValuativeCriterion.Existence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop where
  /-- Every valuative square admits a dominating extension with a lifted point. -/
  nonempty_extension : ∀ sq : ValuativeCommSq F, Nonempty sq.Extension

namespace ValuativeCriterion.Existence

/-- The constant functor at the terminal type satisfies the existence part of
the valuative criterion. -/
instance instConst {S : Scheme.{u}} {B : AlgebraicSpace S} :
    Existence ((Functor.const ((SchemesOver B)ᵒᵖ)).obj PUnit.{u + 2}) :=
  sorry

/-- A functor satisfies existence if and only if every valuative square admits a
dominating extension with a lifted point. -/
theorem spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (F : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)) :
    Existence F ↔ ∀ sq : ValuativeCommSq F, Nonempty sq.Extension :=
  sorry

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicSpace.Quot
