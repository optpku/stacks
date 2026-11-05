/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import ReasLib.RingTheory.Valuation.Extension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare

/-!
# Existence part of the valuative criterion for algebraic stacks

A morphism of algebraic stacks satisfies the existence part of the valuative
criterion when every solid 2-commutative valuative square admits a dominating
extension of valuation rings together with a dotted arrow of the induced outer
rectangle.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace ValuativeCommSq

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}

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
        Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom := by
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq sq.R sq.K K',
    ← IsScalarTower.algebraMap_eq sq.R R' K']

/- The schemes and solid arrows of an extension, before choosing a dotted arrow.
The constructions use only the indicated ring maps; the valuation and
fraction-field hypotheses remain on the valuative extension interface. -/
namespace ExtensionBase

/-- `Spec(R')` over the base, induced by `R → R'`. -/
abbrev specR (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    [Algebra sq.R R'] : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom)

/-- `Spec(K')` over the base, with structure map through `R'`. -/
abbrev specK (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra R' K'] : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
    Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom)

/-- The solid arrow `Spec(R') ⟶ Spec(R)`. -/
abbrev toSpecR (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    [Algebra sq.R R'] :
    GroupoidsOver.slice (specR sq R') ⟶ GroupoidsOver.slice sq.specR :=
  overMap (Over.homMk (U := specR sq R') (V := sq.specR)
    (Spec.map (CommRingCat.ofHom (algebraMap sq.R R'))) rfl)

/-- The solid arrow `Spec(K') ⟶ Spec(K)`, using compatibility over the base. -/
abbrev toSpecK (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K'] [Algebra R' K']
    (specK_compat :
      Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom =
        Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
          Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) :
    GroupoidsOver.slice (specK sq R' K') ⟶ GroupoidsOver.slice sq.specK :=
  overMap (Over.homMk (U := specK sq R' K') (V := sq.specK)
    (Spec.map (CommRingCat.ofHom (algebraMap sq.K K'))) specK_compat)

/-- The solid vertical arrow `Spec(K') ⟶ Spec(R')`. -/
abbrev verticalMap (sq : ValuativeCommSq f) (R' : Type u) [CommRing R']
    (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra R' K'] :
    GroupoidsOver.slice (specK sq R' K') ⟶ GroupoidsOver.slice (specR sq R') :=
  overMap (Over.homMk (U := specK sq R' K') (V := specR sq R')
    (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) rfl)

end ExtensionBase

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
    ExtensionBase.verticalMap sq R' K' ≫
        ExtensionBase.toSpecR sq R' =
      ExtensionBase.toSpecK sq R' K' specK_compat ≫
        sq.verticalMap := by
  unfold ExtensionBase.verticalMap ExtensionBase.toSpecR ExtensionBase.toSpecK
    ValuativeCommSq.verticalMap
  rw [← overMap.comp, ← overMap.comp]
  congr 1
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
      Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) =
    Spec.map (CommRingCat.ofHom (algebraMap sq.K K')) ≫
      Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))
  rw [← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq sq.R R' K',
    ← IsScalarTower.algebraMap_eq sq.R sq.K K']

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
    ExtensionBase.verticalMap sq R' K' ≫
        (ExtensionBase.toSpecR sq R' ≫ sq.i₂) ≅
      (ExtensionBase.toSpecK sq R' K' specK_compat ≫
          sq.i₁) ≫
        f :=
  let j' := ExtensionBase.verticalMap sq R' K'
  let toSpecR := ExtensionBase.toSpecR sq R'
  let toSpecK :=
    ExtensionBase.toSpecK sq R' K' specK_compat
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
      (ExtensionBase.toSpecR sq R' ≫ sq.i₂) f where
  pt := GroupoidsOver.slice (ExtensionBase.specK sq R' K')
  fst := ExtensionBase.verticalMap sq R' K'
  snd :=
    ExtensionBase.toSpecK sq R' K' specK_compat ≫ sq.i₁
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
      inducedOuterIso sq R' K' specK_compat :=
  rfl

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
  @ExtensionBase.specR S X Y _ _ f sq e.R' e.commRing e.algebra_R

/-- `Spec(K')` as a scheme over `S`, via the algebra map `R' → K'`. -/
abbrev specK' {sq : ValuativeCommSq f} (e : Extension sq) : Over S :=
  @ExtensionBase.specK S X Y _ _ f sq e.R' e.commRing e.K' e.field
    e.algebra_R e.algebra

/-- The morphism `Spec(R') ⟶ Spec(R)` of algebraic stacks over `S`. -/
abbrev toSpecR {sq : ValuativeCommSq f} (e : Extension sq) :
    GroupoidsOver.slice e.specR' ⟶ GroupoidsOver.slice sq.specR :=
  @ExtensionBase.toSpecR S X Y _ _ f sq e.R' e.commRing e.algebra_R

/-- The morphism `Spec(K') ⟶ Spec(K)` of algebraic stacks over `S`. -/
abbrev toSpecK {sq : ValuativeCommSq f} (e : Extension sq) :
    GroupoidsOver.slice e.specK' ⟶ GroupoidsOver.slice sq.specK :=
  @ExtensionBase.toSpecK S X Y _ _ f sq e.R' e.commRing e.K' e.field
    e.algebra_R e.algebra_K e.algebra e.specK_compat

/-- The vertical morphism `Spec(K') ⟶ Spec(R')` of algebraic stacks over `S`. -/
abbrev verticalMap {sq : ValuativeCommSq f} (e : Extension sq) :
    GroupoidsOver.slice e.specK' ⟶ GroupoidsOver.slice e.specR' :=
  @ExtensionBase.verticalMap S X Y _ _ f sq e.R' e.commRing e.K' e.field
    e.algebra_R e.algebra

/-- `specR'` is `Over.mk` of the structure morphism of `Spec(R')`. -/
theorem specR'_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.specR' =
      Over.mk (Spec.map e.ringMap ≫ sq.structureHom) :=
  rfl

/-- `specK'` is `Over.mk` of the structure morphism of `Spec(K')` via `R'`. -/
theorem specK'_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.specK' =
      Over.mk
        (Spec.map e.fractionMap ≫
          Spec.map e.ringMap ≫ sq.structureHom) :=
  rfl

/-- The map to the original ring spectrum is induced by the bundled ring extension. -/
theorem toSpecR_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.toSpecR = overMap (Over.homMk (U := e.specR') (V := sq.specR) (Spec.map e.ringMap) rfl) :=
  rfl

/-- The map to the original field spectrum is induced by the bundled field extension. -/
theorem toSpecK_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.toSpecK =
      overMap (Over.homMk (U := e.specK') (V := sq.specK) (Spec.map e.fieldMap) e.specK_compat) :=
  rfl

/-- The extended vertical map is induced by the bundled fraction-field map. -/
theorem verticalMap_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.verticalMap = overMap (Over.homMk (U := e.specK') (V := e.specR') (Spec.map e.fractionMap) rfl) :=
  rfl

/-- The two paths `Spec(K') ⟶ Spec(R)` of an extended valuative square agree. -/
theorem verticalMap_comp_toSpecR {sq : ValuativeCommSq f} (e : Extension sq) :
    e.verticalMap ≫ e.toSpecR = e.toSpecK ≫ sq.verticalMap :=
  @verticalMap_comp_toSpecR_of S X Y _ _ f sq e.R' e.commRing e.domain
    e.valuationRing e.K' e.field e.algebra_R e.algebra_K e.algebra e.algebra_base
    e.isFractionRing e.isExtension e.isScalarTower_K e.isScalarTower_R' e.specK_compat

/-- The solid outer rectangle of an extended valuative square, as a
2-commutative cospan cone. -/
abbrev outerCone {sq : ValuativeCommSq f} (e : Extension sq) :
    Bicategory.PseudoPullbackCone (e.toSpecR ≫ sq.i₂) f :=
  @inducedOuterCone S X Y inferInstance inferInstance f sq e.R' e.commRing
    e.domain e.valuationRing e.K' e.field e.algebra_R e.algebra_K e.algebra
    e.algebra_base e.isFractionRing e.isExtension e.isScalarTower_K
    e.isScalarTower_R' e.specK_compat

/-- The apex of `outerCone` is the slice of `Spec(K')`. -/
theorem outerCone_pt {sq : ValuativeCommSq f} (e : Extension sq) :
    (outerCone e).pt = GroupoidsOver.slice e.specK' :=
  rfl

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

/-- The dominating valuation ring of `Extension.of` is the given ring. -/
theorem of_R' (sq : ValuativeCommSq f) (R' : Type u) [CommRing R'] [IsDomain R']
    [ValuationRing R'] (K' : Type u) [Field K'] [Algebra sq.R R'] [Algebra sq.K K']
    [Algebra R' K'] [Algebra sq.R K'] [IsFractionRing R' K']
    [IsExtensionOfValuationRings sq.R R'] [IsScalarTower sq.R sq.K K']
    [IsScalarTower sq.R R' K']
    (lift : DottedArrow (inducedOuterCone sq R' K' (specK_compat_of sq R' K'))) :
    (of sq R' K' lift).R' = R' :=
  rfl

/-- The dotted morphism `Spec(R') ⟶ X` filling the extended valuative diagram. -/
abbrev liftArrow {sq : ValuativeCommSq f} (e : Extension sq) :
    GroupoidsOver.slice e.specR' ⟶ X :=
  e.lift.arrow

/-- `liftArrow` is the dotted 1-morphism of the stored dotted arrow. -/
theorem liftArrow_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    e.liftArrow = e.lift.arrow :=
  rfl

/-- The upper-left triangle of an extended valuative square: `Spec(K') ⟶ Spec(R') ⟶ X`
is 2-isomorphic to `Spec(K') ⟶ Spec(K) ⟶ X`. -/
def fac_left {sq : ValuativeCommSq f} (e : Extension sq) :
    e.verticalMap ≫ e.liftArrow ≅ e.toSpecK ≫ sq.i₁ :=
  e.lift.left

/-- The lower-right triangle of an extended valuative square: `Spec(R') ⟶ Y`
is 2-isomorphic to `Spec(R') ⟶ X ⟶ Y`. -/
def fac_right {sq : ValuativeCommSq f} (e : Extension sq) :
    e.toSpecR ≫ sq.i₂ ≅ e.liftArrow ≫ f :=
  e.lift.right

/-- The first projection of `fac_left` is the upper-left comparison of the dotted
arrow. -/
theorem fac_left_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    fac_left e = e.lift.left :=
  rfl

/-- The first projection of `fac_right` is the lower-right comparison of the
dotted arrow. -/
theorem fac_right_eq {sq : ValuativeCommSq f} (e : Extension sq) :
    fac_right e = e.lift.right :=
  rfl

end Extension

end ValuativeCommSq

/-- A morphism of algebraic stacks satisfies the existence part of the valuative
criterion if every valuative commutative square admits a dominating extension
together with a dotted arrow of the extended rectangle. -/
@[mk_iff]
class ValuativeCriterion.Existence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- Every valuative square admits a dominating extension with a dotted arrow. -/
  nonempty_extension : ∀ sq : ValuativeCommSq f, Nonempty sq.Extension

namespace ValuativeCriterion.Existence

/-- The identity morphism of an algebraic stack satisfies the existence part of
the valuative criterion. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Existence (𝟙 X) :=
  sorry

/-- A morphism satisfies existence if and only if every valuative square admits a
dominating extension with a dotted arrow. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Existence f ↔ ∀ sq : ValuativeCommSq f, Nonempty sq.Extension :=
  sorry

/-- The composite of two morphisms of algebraic stacks satisfying the existence
part of the valuative criterion also satisfies that criterion. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Existence f] [Existence g] :
    Existence (f ≫ g) :=
  sorry

end ValuativeCriterion.Existence

end AlgebraicGeometry.AlgebraicStack
