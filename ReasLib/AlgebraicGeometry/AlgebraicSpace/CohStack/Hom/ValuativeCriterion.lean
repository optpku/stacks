module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.RingTheory.Valuation.Extension
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Existence part of the valuative criterion at CohStack size

A 1-morphism in `FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)`
satisfies the existence part of the valuative criterion when every solid
2-commutative valuative square admits a dominating extension of valuation rings
together with a dotted arrow of the induced outer rectangle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupScheme
open CategoryTheory.BasedFunctor
open CategoryTheory.FiberedCategoryOver.Groupoids
open scoped Bicategory
open scoped CategoryTheory.BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

open Classifying

/-- A valuative commutative square over a 1-morphism `f : X ⟶ Y` of groupoid
fibrations over `Over S`, in the Hom-universe of `CohStack.toGroupoids`, is a
solid 2-commutative diagram `Spec(K) ⟶ X`, `Spec(R) ⟶ Y` with vertical arrow
`Spec(K) ⟶ Spec(R)`, where `R` is a valuation ring and `K` is a field of
fractions of `R`. -/
structure ValuativeCommSq {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) where
  /-- The underlying scheme-valued square over the identity of the base. -/
  baseSquare : AlgebraicGeometry.ValuativeCommSq (𝟙 S)
  /-- The top map `Spec(K) ⟶ X` of groupoid fibrations over `S`. -/
  i₁ :
    Classifying.slice
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap baseSquare.R baseSquare.K)) ≫ baseSquare.i₂)) ⟶
      X
  /-- The bottom map `Spec(R) ⟶ Y` of groupoid fibrations over `S`. -/
  i₂ : Classifying.slice (Over.mk baseSquare.i₂) ⟶ Y
  /-- The 2-cell `j ≫ y ≅ x ≫ f` witnessing 2-commutativity of the solid square. -/
  iso :
    Classifying.overMap
        (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap baseSquare.R baseSquare.K))) rfl) ≫
      i₂ ≅
      i₁ ≫ f

namespace ValuativeCommSq

variable {S : Scheme.{u}}
variable {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
variable {f : X ⟶ Y}

/-- The valuation domain of a valuative square. -/
abbrev R (sq : ValuativeCommSq f) : Type u := sq.baseSquare.R

/-- The commutative ring structure of the valuation domain. -/
abbrev commRing (sq : ValuativeCommSq f) : CommRing sq.R := sq.baseSquare.commRing

/-- The valuation ring is an integral domain. -/
abbrev domain (sq : ValuativeCommSq f) : IsDomain sq.R := sq.baseSquare.domain

/-- The valuation-ring structure of the domain. -/
abbrev valuationRing (sq : ValuativeCommSq f) : ValuationRing sq.R :=
  sq.baseSquare.valuationRing

/-- The fraction field of a valuative square. -/
abbrev K (sq : ValuativeCommSq f) : Type u := sq.baseSquare.K

/-- The field structure of the fraction field. -/
abbrev field (sq : ValuativeCommSq f) : Field sq.K := sq.baseSquare.field

/-- The algebra structure from the valuation domain to its fraction field. -/
abbrev algebra (sq : ValuativeCommSq f) : Algebra sq.R sq.K := sq.baseSquare.algebra

/-- The field is a fraction ring of the valuation domain. -/
abbrev isFractionRing (sq : ValuativeCommSq f) : IsFractionRing sq.R sq.K :=
  sq.baseSquare.isFractionRing

/-- The structure morphism of the valuation-ring spectrum over the base. -/
abbrev structureHom (sq : ValuativeCommSq f) : Spec (.of sq.R) ⟶ S :=
  sq.baseSquare.i₂

/-- Construct a valuative commutative square from a valuation ring, a field of
fractions, a structure morphism over `S`, the two solid arrows, and a 2-cell. -/
def of (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₁ :
      Classifying.slice
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶
        X)
    (i₂ : Classifying.slice (Over.mk structureHom) ⟶ Y)
    (iso :
      Classifying.overMap
          (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl) ≫
        i₂ ≅
        i₁ ≫ f) :
    ValuativeCommSq f where
  baseSquare :=
    { R := R
      K := K
      i₁ := Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom
      i₂ := structureHom
      commSq := ⟨Category.comp_id _⟩ }
  i₁ := i₁
  i₂ := i₂
  iso := iso

/-- The two solid arrows and their invertible comparison are those supplied to the constructor. -/
theorem of_spec (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₁ :
      Classifying.slice
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶
        X)
    (i₂ : Classifying.slice (Over.mk structureHom) ⟶ Y)
    : ∀ iso,
    let sq : ValuativeCommSq f :=
      of (S := S) (X := X) (Y := Y) (f := f) R K structureHom i₁ i₂ iso
    HEq sq.i₁ i₁ ∧ HEq sq.i₂ i₂ ∧ HEq sq.iso iso := sorry

/-- `Spec(R)` as a scheme over `S`. -/
abbrev specR (sq : ValuativeCommSq f) : Over S := Over.mk sq.structureHom

/-- `Spec(K)` as a scheme over `S`, via the algebra map `R → K`. -/
abbrev specK (sq : ValuativeCommSq f) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom)

/-- The vertical morphism `Spec(K) ⟶ Spec(R)` of groupoid fibrations over `S`. -/
abbrev verticalMap (sq : ValuativeCommSq f) :
    Classifying.slice sq.specK ⟶ Classifying.slice sq.specR :=
  Classifying.overMap
    (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl)

/-- The 2-cell `j ≫ y ≅ x ≫ f` of a solid valuative square. -/
def two_commute (sq : ValuativeCommSq f) :
    sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f :=
  sq.iso

/-- The solid valuative square, viewed as a 2-commutative cospan cone. -/
def toCone (sq : ValuativeCommSq f) : Bicategory.PseudoPullbackCone sq.i₂ f where
  pt := Classifying.slice sq.specK
  fst := sq.verticalMap
  snd := sq.i₁
  iso := sq.iso

/-- Reconstructing a valuative square from its fields recovers the valuation ring. -/
theorem of_R (sq : ValuativeCommSq f) :
    (of sq.R sq.K sq.structureHom sq.i₁ sq.i₂ sq.iso).R = sq.R := sorry

/-- `specR` is `Over.mk` of the structure morphism of `Spec(R)`. -/
theorem specR_eq (sq : ValuativeCommSq f) :
    sq.specR = Over.mk sq.structureHom := sorry

/-- `specK` is `Over.mk` of the structure morphism of `Spec(K)`. -/
theorem specK_eq (sq : ValuativeCommSq f) :
    sq.specK =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom) := sorry

/-- The vertical arrow is `overMap` of `Over.homMk` of `Spec.map` of the algebra map. -/
theorem verticalMap_eq (sq : ValuativeCommSq f) :
    sq.verticalMap =
      Classifying.overMap
        (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl) := sorry

/-- `two_commute` is the stored 2-cell of the valuative square. -/
theorem two_commute_eq (sq : ValuativeCommSq f) : two_commute sq = sq.iso := sorry

/-- The apex of `toCone` is the slice of `Spec(K)`. -/
theorem toCone_pt (sq : ValuativeCommSq f) :
    sq.toCone.pt = Classifying.slice sq.specK := sorry

/-- The two structure morphisms `Spec(K') ⟶ S` obtained via `K` and via `R'`
agree. -/
theorem specK_compat_of (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    [IsDomain R'] [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R']
    [Algebra sq.K K'] [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K'] :
    Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom := sorry

/-- The two paths `Spec(K') ⟶ Spec(R)` of an extended valuative square agree. -/
theorem verticalMap_comp_toSpecR_of (sq : ValuativeCommSq f) (R' : Type u)
    [CommRing R'] [IsDomain R'] [ValuationRing R'] (K' : Type u) [Field K']
    [Algebra sq.R R'] [Algebra sq.K K'] [Algebra R' K'] [Algebra sq.R K']
    [IsFractionRing R' K'] [IsExtensionOfValuationRings sq.R R']
    [IsScalarTower sq.R sq.K K'] [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl ≫
        Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl =
      Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K')))
          specK_compat ≫
        sq.verticalMap := sorry

/-- The induced outer 2-cell of an extended valuative rectangle, obtained by
whiskering the original 2-cell along `Spec(K') ⟶ Spec(K)` and reassociating
along the commuting Spec square. -/
def inducedOuterIso (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    [IsDomain R'] [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R']
    [Algebra sq.K K'] [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl ≫
        (Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl ≫
          sq.i₂) ≅
      (Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K')))
            specK_compat ≫
          sq.i₁) ≫
        f :=
  let j' := Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl
  let toSpecR :=
    Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl
  let toSpecK :=
    Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K')))
      specK_compat
  (α_ j' toSpecR sq.i₂).symm ≪≫
    eqToIso (verticalMap_comp_toSpecR_of sq R' K' specK_compat) ▷ᵢ sq.i₂ ≪≫
    α_ toSpecK sq.verticalMap sq.i₂ ≪≫
    toSpecK ◁ᵢ sq.iso ≪≫
    (α_ toSpecK sq.i₁ f).symm

/-- The solid outer rectangle of an extended valuative square, as a
2-commutative cospan cone whose 2-cell is the induced whiskering of the
original 2-cell. -/
def inducedOuterCone (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    [IsDomain R'] [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R']
    [Algebra sq.K K'] [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    Bicategory.PseudoPullbackCone
      (Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl ≫
        sq.i₂)
      f where
  pt :=
    Classifying.slice
      (Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom))
  fst := Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl
  snd :=
    Classifying.sliceHomMk (Spec.map (CommRingCat.ofHom (algebraMap sq.K K')))
        specK_compat ≫
      sq.i₁
  iso := inducedOuterIso sq R' K' specK_compat

/-- The 2-cell of `inducedOuterCone` is the induced whiskering `inducedOuterIso`. -/
theorem inducedOuterCone_iso (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    [IsDomain R'] [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R']
    [Algebra sq.K K'] [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    (inducedOuterCone sq R' K' specK_compat).iso =
      inducedOuterIso sq R' K' specK_compat := sorry

/-- An extension of a valuative commutative square is a field extension `K'/K`,
a valuation ring `R'` of `K'` dominating `R`, and a dotted arrow filling the
induced outer rectangle. -/
structure Extension (sq : ValuativeCommSq f) where
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
  /-- A dotted arrow of the induced outer rectangle. -/
  lift : DottedArrow (inducedOuterCone sq R' K' specK_compat)

namespace Extension

/-- The dominating valuation ring as a bundled commutative ring. -/
def ringObj {sq : ValuativeCommSq f} (e : Extension sq) : CommRingCat.{u} :=
  @CommRingCat.of e.R' e.commRing

/-- The extended fraction field as a bundled commutative ring. -/
def fieldObj {sq : ValuativeCommSq f} (e : Extension sq) : CommRingCat.{u} :=
  @CommRingCat.of e.K' e.field.toCommRing

/-- The bundled algebra map from the original valuation ring to the dominating ring. -/
def ringMap {sq : ValuativeCommSq f} (e : Extension sq) :
    CommRingCat.of sq.R ⟶ e.ringObj :=
  CommRingCat.ofHom (R := CommRingCat.of sq.R) (S := e.ringObj)
    (@algebraMap (CommRingCat.of sq.R) e.ringObj _ _ e.algebra_R)

/-- The bundled algebra map from the original fraction field to the extended field. -/
def fieldMap {sq : ValuativeCommSq f} (e : Extension sq) :
    CommRingCat.of sq.K ⟶ e.fieldObj :=
  CommRingCat.ofHom (R := CommRingCat.of sq.K) (S := e.fieldObj)
    (@algebraMap (CommRingCat.of sq.K) e.fieldObj _ _ e.algebra_K)

/-- The bundled algebra map from the dominating valuation ring to its fraction field. -/
def fractionMap {sq : ValuativeCommSq f} (e : Extension sq) :
    e.ringObj ⟶ e.fieldObj :=
  CommRingCat.ofHom (R := e.ringObj) (S := e.fieldObj)
    (@algebraMap e.ringObj e.fieldObj _ _ e.algebra)

/-- `Spec(R')` as a scheme over `S`, via the algebra map `R → R'`. -/
abbrev specR' {sq : ValuativeCommSq f} (e : Extension sq) : Over S :=
  Over.mk (Spec.map e.ringMap ≫ sq.structureHom)

/-- `Spec(K')` as a scheme over `S`, via the algebra map `R' → K'`. -/
abbrev specK' {sq : ValuativeCommSq f} (e : Extension sq) : Over S :=
  Over.mk
    (Spec.map e.fractionMap ≫
      Spec.map e.ringMap ≫ sq.structureHom)

/-- The morphism `Spec(R') ⟶ Spec(R)` of groupoid fibrations over `S`. -/
abbrev toSpecR {sq : ValuativeCommSq f} (e : Extension sq) :
    Classifying.slice e.specR' ⟶ Classifying.slice sq.specR :=
  Classifying.overMap (Over.homMk (U := e.specR') (V := sq.specR) (Spec.map e.ringMap) rfl)

/-- The morphism `Spec(K') ⟶ Spec(K)` of groupoid fibrations over `S`. -/
abbrev toSpecK {sq : ValuativeCommSq f} (e : Extension sq) :
    Classifying.slice e.specK' ⟶ Classifying.slice sq.specK :=
  Classifying.overMap (Over.homMk (U := e.specK') (V := sq.specK) (Spec.map e.fieldMap) e.specK_compat)

/-- The vertical morphism `Spec(K') ⟶ Spec(R')` of groupoid fibrations over `S`. -/
abbrev verticalMap {sq : ValuativeCommSq f} (e : Extension sq) :
    Classifying.slice e.specK' ⟶ Classifying.slice e.specR' :=
  Classifying.overMap (Over.homMk (U := e.specK') (V := e.specR') (Spec.map e.fractionMap) rfl)

/-- The solid outer rectangle of an extended valuative square, as a
2-commutative cospan cone. -/
abbrev outerCone {sq : ValuativeCommSq f} (e : Extension sq) :
    Bicategory.PseudoPullbackCone (e.toSpecR ≫ sq.i₂) f :=
  @inducedOuterCone S X Y f sq e.R' e.commRing
    e.domain e.valuationRing e.K' e.field e.algebra_R e.algebra_K e.algebra
    e.algebra_base e.isFractionRing e.isExtension e.isScalarTower_K
    e.isScalarTower_R' e.specK_compat

/-- Construct an extension of a valuative square from dominating valuation-ring
data and a dotted arrow of the induced outer cone. -/
def of (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (lift : DottedArrow (inducedOuterCone sq R' K' (specK_compat_of sq R' K'))) :
    Extension sq where
  R' := R'
  K' := K'
  specK_compat := specK_compat_of sq R' K'
  lift := lift

/-- The dotted morphism `Spec(R') ⟶ X` filling the extended valuative diagram. -/
abbrev liftArrow {sq : ValuativeCommSq f} (e : Extension sq) :
    Classifying.slice e.specR' ⟶ X :=
  e.lift.arrow

/-- The upper-left triangle of an extended valuative square. -/
def fac_left {sq : ValuativeCommSq f} (e : Extension sq) :
    e.verticalMap ≫ e.liftArrow ≅ e.toSpecK ≫ sq.i₁ :=
  e.lift.left

/-- The lower-right triangle of an extended valuative square. -/
def fac_right {sq : ValuativeCommSq f} (e : Extension sq) :
    e.toSpecR ≫ sq.i₂ ≅ e.liftArrow ≫ f :=
  e.lift.right

/-- The dominating valuation ring of `Extension.of` is the given ring. -/
theorem of_R' (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (lift : DottedArrow (inducedOuterCone sq R' K' (specK_compat_of sq R' K'))) :
    (of sq R' K' lift).R' = R' := sorry

/-- The extension constructor preserves the supplied valuation ring, fraction field,
and dotted arrow of the induced outer rectangle. -/
theorem of_spec (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (lift : DottedArrow (inducedOuterCone sq R' K' (specK_compat_of sq R' K'))) :
    (of sq R' K' lift).R' = R' ∧ (of sq R' K' lift).K' = K' ∧
      HEq (of sq R' K' lift).lift lift := sorry

/-- `specR'` is `Over.mk` of the structure morphism of `Spec(R')`. -/
theorem specR'_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.specR' =
      Over.mk (Spec.map (e.ringMap) ≫ sq.structureHom) := sorry

/-- `specK'` is `Over.mk` of the structure morphism of `Spec(K')` via `R'`. -/
theorem specK'_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.specK' =
      Over.mk
        (Spec.map (e.fractionMap) ≫
          Spec.map (e.ringMap) ≫ sq.structureHom) := sorry

/-- `liftArrow` is the dotted 1-morphism of the stored dotted arrow. -/
theorem liftArrow_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.liftArrow = e.lift.arrow := sorry

/-- The first projection of `fac_left` is the upper-left comparison of the dotted
arrow. -/
theorem fac_left_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    fac_left e = e.lift.left := sorry

/-- The first projection of `fac_right` is the lower-right comparison of the
dotted arrow. -/
theorem fac_right_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    fac_right e = e.lift.right := sorry

end Extension

end ValuativeCommSq

/-- A 1-morphism of groupoid fibrations over `Over S`, in the Hom-universe of
`CohStack.toGroupoids`, satisfies the existence part of the valuative criterion
if every valuative commutative square admits a dominating extension together
with a dotted arrow of the extended rectangle. -/
@[mk_iff]
class ValuativeCriterion.Existence {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- Every valuative square admits a dominating extension with a dotted arrow. -/
  nonempty_extension : ∀ sq : ValuativeCommSq f, Nonempty sq.Extension

namespace ValuativeCriterion.Existence

/-- The identity 1-morphism of a groupoid fibration satisfies the existence part
of the valuative criterion. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    Existence (𝟙 X) := sorry

/-- A 1-morphism satisfies existence if and only if every valuative square admits
a dominating extension with a dotted arrow. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Existence f ↔ ∀ sq : ValuativeCommSq f, Nonempty sq.Extension := sorry

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
