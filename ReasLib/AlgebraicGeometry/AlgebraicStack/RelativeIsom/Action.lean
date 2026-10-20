/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Comparison

/-!
# Postcomposition action of relative automorphisms on relative isomorphisms

The sheaf `Isom^α_{X/Y}(x1, x2)` is an algebraic space over `Z`, and
`Isom_{X/Y}(x2, x2)` acts on it by postcomposition in the homotopy category of
algebraic spaces over `Z`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.RelativeInertia
open AlgebraicGeometry.SpacesOver
open scoped Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

/-- The relative isomorphism sheaf is an algebraic stack. -/
instance instAlgebraicStack_relativeIsom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    AlgebraicStack (relativeIsom f α) :=
  sorry

/-- The structure morphism `Isom^α_{X/Y}(x1, x2) ⟶ Z` is locally of finite type. -/
instance instLocallyOfFiniteType_relativeIsom_snd {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    Groupoids.Hom.LocallyOfFiniteType (relativeIsom.snd f α) :=
  sorry

/-- The relative isomorphism sheaf, as an object of `SpacesOver` of
`Z.toGroupoids`. -/
def asSpacesOverIsom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    SpacesOver Z.toGroupoids :=
  SpacesOver.mk (relativeIsom.snd f α)
    (Groupoids.Hom.LocallyOfFiniteType.relativelyRepresentable _)

/-- The domain of `asSpacesOverIsom f α` is `relativeIsom f α`. -/
theorem asSpacesOverIsom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    SpacesOver.left (asSpacesOverIsom f α) = relativeIsom f α :=
  rfl

/-- The structural morphism of `asSpacesOverIsom f α` is `relativeIsom.snd f α`. -/
theorem asSpacesOverIsom_hom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    SpacesOver.hom (asSpacesOverIsom f α) = relativeIsom.snd f α :=
  rfl

/-- Packaged relative isomorphisms have algebraic-stack domain, and the
structure map to `Z` is representable by algebraic spaces. -/
theorem asSpacesOverIsom_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    AlgebraicStack (SpacesOver.left (asSpacesOverIsom f α)) ∧
      relativelyRepresentableByAlgebraicSpaces
        (SpacesOver.hom (asSpacesOverIsom f α)) :=
  SpacesOver.spec (asSpacesOverIsom f α)

/-- Relative isomorphisms as an object of the homotopy 1-category of
algebraic-space representable morphisms to `Z`. -/
def asHomotopyIsom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Bicategory.HomotopyCategory (SpacesOver Z.toGroupoids) :=
  Bicategory.HomotopyCategory.mk (asSpacesOverIsom f α)

/-- The underlying `SpacesOver` object of `asHomotopyIsom f α` is
`asSpacesOverIsom f α`. -/
theorem asHomotopyIsom_as {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    (asHomotopyIsom f α).as = asSpacesOverIsom f α :=
  rfl

/-- The chosen 2-fibre product of relative automorphisms of `x2` with
`Isom^α_{X/Y}(x1, x2)` over `Z`. -/
abbrev smulApex {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} (fst f x2) (relativeIsom.snd f α)

/-- The structure morphism of the product
`Isom_{X/Y}(x2, x2) ×_Z Isom^α_{X/Y}(x1, x2)` over `Z`. -/
def smulStructure {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulApex f α ⟶ Z.toGroupoids :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x2) (relativeIsom.snd f α) ≫
    fst f x2

/-- The universal relative automorphism commutes with inertia morphisms. -/
private theorem Implementation.tautologicalAut_naturality {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {ξ ζ : (relativeInertia.{u + 1, u, u, u + 1} f).total} (g : ξ ⟶ ζ) :
    (toFunctor (forget.{u + 1, u, u, u + 1} f)).map g ≫ ζ.aut.hom =
      ξ.aut.hom ≫ (toFunctor (forget.{u + 1, u, u, u + 1} f)).map g :=
  sorry

/-- The universal relative automorphism lies over the identity of its base. -/
private theorem Implementation.tautologicalAut_isHomLift {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (ξ : (relativeInertia.{u + 1, u, u, u + 1} f).total) :
    X.p.IsHomLift (𝟙 ((relativeInertia.{u + 1, u, u, u + 1} f).p.obj ξ))
      ξ.aut.hom :=
  sorry

/-- The tautological fibre automorphism of the universal object of relative
inertia. -/
private def Implementation.tautologicalAut {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    forget.{u + 1, u, u, u + 1} f ≅ forget.{u + 1, u, u, u + 1} f :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (fun ξ ↦ ξ.aut)
      (fun g ↦ Implementation.tautologicalAut_naturality f g) (Implementation.tautologicalAut_isHomLift f))

/-- Identifying `x2` with the underlying object of relative inertia, along the
automorphism factor of the product over `Z`. -/
private def Implementation.smulAutIdent {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulStructure f α ≫ x2 ≅
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x2)
            (relativeIsom.snd f α) ≫
          snd f x2) ≫
        forget.{u + 1, u, u, u + 1} f :=
  α_ _ _ _ ≪≫
    whiskerLeftIso
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x2)
          (relativeIsom.snd f α))
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} x2
          (forget.{u + 1, u, u, u + 1} f)) ≪≫
      (α_ _ _ _).symm

/-- The relative automorphism factor as a 2-endomorphism of `x2` over `Z`. -/
private def Implementation.smulAutIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulStructure f α ≫ x2 ≅ smulStructure f α ≫ x2 :=
  Implementation.smulAutIdent f α ≪≫
    whiskerLeftIso
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (fst f x2)
            (relativeIsom.snd f α) ≫
          snd f x2)
        (Implementation.tautologicalAut f) ≪≫
      (Implementation.smulAutIdent f α).symm

/-- The isomorphism factor of the product, as a 2-cell `x1 ≅ x2` over `Z`. -/
private def Implementation.smulIsomIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulStructure f α ≫ x1 ≅ smulStructure f α ≫ x2 :=
  whiskerRightIso
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} (fst f x2)
        (relativeIsom.snd f α))
      x1 ≪≫
    α_ _ _ _ ≪≫
      whiskerLeftIso
          (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (fst f x2)
            (relativeIsom.snd f α))
          (relativeIsom.compIso f α) ≪≫
        (α_ _ _ _).symm ≪≫
          whiskerRightIso
              (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} (fst f x2)
                (relativeIsom.snd f α)).symm
              x2

/-- Postcomposition of fibre isomorphisms `(φ, β) ↦ φ ≫ β` as a 2-cell over `Z`. -/
private def Implementation.smulCompIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulStructure f α ≫ x1 ≅ smulStructure f α ≫ x2 :=
  Implementation.smulIsomIso f α ≪≫ Implementation.smulAutIso f α

/-- The cone over `x1, x2` presenting postcomposition of isomorphisms. -/
private def Implementation.smulToPairCone {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Bicategory.PseudoPullbackCone x1 x2 where
  pt := smulApex f α
  fst := smulStructure f α
  snd := smulStructure f α
  iso := Implementation.smulCompIso f α

/-- Postcomposition of the automorphism factor with the isomorphism factor,
as a map into the pair product `Z ×_X Z`. -/
private def Implementation.smulToPair {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulApex f α ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2 :=
  Bicategory.PseudoPullbackCone.lift (Implementation.smulToPairCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x1 x2)

/-- Postcomposition followed by the first `Z`-leg of the pair product `Z ×_X Z` recovers
the structure morphism over `Z`. -/
private def Implementation.smulToPair_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Implementation.smulToPair f α ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} x1 x2 ≅
      smulStructure f α :=
  Bicategory.PseudoPullbackCone.lift.fstIso (Implementation.smulToPairCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x1 x2)

/-- Postcomposition followed by the second `Z`-leg of the pair product `Z ×_X Z` recovers
the structure morphism over `Z`. -/
private def Implementation.smulToPair_snd {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Implementation.smulToPair f α ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} x1 x2 ≅
      smulStructure f α :=
  Bicategory.PseudoPullbackCone.lift.sndIso (Implementation.smulToPairCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x1 x2)

/-- After applying `f`, postcomposition and the original isomorphism have the
same first projection to `Z`. -/
private def Implementation.smulIsoLegsFst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Implementation.smulToPair f α ≫ pairComparison f x1 x2 ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) ≅
      smulStructure f α ≫ diagonalAlpha α ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) :=
  whiskerLeftIso (Implementation.smulToPair f α)
      (TwoFibreProduct.map.fstIso (pairComparisonCospan f x1 x2)) ≪≫
    whiskerLeftIso (Implementation.smulToPair f α) (ρ_ _) ≪≫
      Implementation.smulToPair_fst f α ≪≫
        (ρ_ (smulStructure f α)).symm ≪≫
          whiskerLeftIso (smulStructure f α) (diagonalAlpha_fst α).symm

/-- After applying `f`, postcomposition and the original isomorphism have the
same second projection to `Z`. -/
private def Implementation.smulIsoLegsSnd {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Implementation.smulToPair f α ≫ pairComparison f x1 x2 ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) ≅
      smulStructure f α ≫ diagonalAlpha α ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f) :=
  whiskerLeftIso (Implementation.smulToPair f α)
      (TwoFibreProduct.map.sndIso (pairComparisonCospan f x1 x2)) ≪≫
    whiskerLeftIso (Implementation.smulToPair f α) (ρ_ _) ≪≫
      Implementation.smulToPair_snd f α ≪≫
        (ρ_ (smulStructure f α)).symm ≪≫
          whiskerLeftIso (smulStructure f α) (diagonalAlpha_snd α).symm

/-- The forward and inverse component comparisons compose to the identity. -/
private theorem Implementation.smulIsoFstObj_hom_inv_id {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    ((toNatTrans (Implementation.smulIsoLegsFst f α).hom).app p) ≫ ((toNatTrans (Implementation.smulIsoLegsFst f α).inv).app p) = 𝟙 _ :=
  sorry

/-- The inverse and forward component comparisons compose to the identity. -/
private theorem Implementation.smulIsoFstObj_inv_hom_id {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    ((toNatTrans (Implementation.smulIsoLegsFst f α).inv).app p) ≫ ((toNatTrans (Implementation.smulIsoLegsFst f α).hom).app p) = 𝟙 _ :=
  sorry

/-- Objectwise first-leg comparison of postcomposition against the diagonal of
`α` in `Isom_Y(f ∘ x1, f ∘ x2)`. -/
private def Implementation.smulIsoFstObj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    BasedCategory.PseudoPullback.fstObj
        ((toFunctor (Implementation.smulToPair f α ≫ pairComparison f x1 x2)).obj p) ≅
      BasedCategory.PseudoPullback.fstObj
        ((toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p) :=
  Iso.mk ((toNatTrans (Implementation.smulIsoLegsFst f α).hom).app p)
    ((toNatTrans (Implementation.smulIsoLegsFst f α).inv).app p)
    (Implementation.smulIsoFstObj_hom_inv_id f α p) (Implementation.smulIsoFstObj_inv_hom_id f α p)

/-- The forward and inverse component comparisons compose to the identity. -/
private theorem Implementation.smulIsoSndObj_hom_inv_id {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    ((toNatTrans (Implementation.smulIsoLegsSnd f α).hom).app p) ≫ ((toNatTrans (Implementation.smulIsoLegsSnd f α).inv).app p) = 𝟙 _ :=
  sorry

/-- The inverse and forward component comparisons compose to the identity. -/
private theorem Implementation.smulIsoSndObj_inv_hom_id {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    ((toNatTrans (Implementation.smulIsoLegsSnd f α).inv).app p) ≫ ((toNatTrans (Implementation.smulIsoLegsSnd f α).hom).app p) = 𝟙 _ :=
  sorry

/-- Objectwise second-leg comparison of postcomposition against the diagonal of
`α` in `Isom_Y(f ∘ x1, f ∘ x2)`. -/
private def Implementation.smulIsoSndObj {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    BasedCategory.PseudoPullback.sndObj
        ((toFunctor (Implementation.smulToPair f α ≫ pairComparison f x1 x2)).obj p) ≅
      BasedCategory.PseudoPullback.sndObj
        ((toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p) :=
  Iso.mk ((toNatTrans (Implementation.smulIsoLegsSnd f α).hom).app p)
    ((toNatTrans (Implementation.smulIsoLegsSnd f α).inv).app p)
    (Implementation.smulIsoSndObj_hom_inv_id f α p) (Implementation.smulIsoSndObj_inv_hom_id f α p)

/-- The component comparison lifts the common base isomorphism. -/
private theorem Implementation.smulIsoApp_fst_isHomLift {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    Z.toGroupoids.p.IsHomLift ((BasedCategory.PseudoPullback.fstBaseIso
          ((toFunctor (Implementation.smulToPair f α ≫ pairComparison f x1 x2)).obj p)).symm ≪≫
      (Z.toGroupoids.p.mapIso (Implementation.smulIsoFstObj f α p)) ≪≫
        BasedCategory.PseudoPullback.fstBaseIso
          ((toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p)).hom
      (Implementation.smulIsoFstObj f α p).hom :=
  sorry

/-- The component comparison lifts the common base isomorphism. -/
private theorem Implementation.smulIsoApp_snd_isHomLift {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    Z.toGroupoids.p.IsHomLift ((BasedCategory.PseudoPullback.fstBaseIso
          ((toFunctor (Implementation.smulToPair f α ≫ pairComparison f x1 x2)).obj p)).symm ≪≫
      (Z.toGroupoids.p.mapIso (Implementation.smulIsoFstObj f α p)) ≪≫
        BasedCategory.PseudoPullback.fstBaseIso
          ((toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p)).hom
      (Implementation.smulIsoSndObj f α p).hom :=
  sorry

/-- Postcomposition by a relative automorphism preserves the prescribed image isomorphism. -/
private theorem Implementation.smulIsoApp_comm {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    CommSq ((toFunctor (x1 ≫ f)).map (Implementation.smulIsoFstObj f α p).hom)
      (BasedCategory.PseudoPullback.comparison ((toFunctor (Implementation.smulToPair f α ≫ pairComparison f x1 x2)).obj p))
      (BasedCategory.PseudoPullback.comparison ((toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p))
      ((toFunctor (x2 ≫ f)).map (Implementation.smulIsoSndObj f α p).hom) :=
  sorry

/-- Objectwise comparison of postcomposition against the diagonal of `α` in
`Isom_Y(f ∘ x1, f ∘ x2)`. -/
private def Implementation.smulIsoApp {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    (toFunctor (Implementation.smulToPair f α ≫ pairComparison f x1 x2)).obj p ≅
      (toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p :=
  BasedCategory.PseudoPullback.mkIso
    ((BasedCategory.PseudoPullback.fstBaseIso
          ((toFunctor (Implementation.smulToPair f α ≫ pairComparison f x1 x2)).obj p)).symm ≪≫
      (Z.toGroupoids.p.mapIso (Implementation.smulIsoFstObj f α p)) ≪≫
        BasedCategory.PseudoPullback.fstBaseIso
          ((toFunctor (smulStructure f α ≫ diagonalAlpha α)).obj p))
    (Implementation.smulIsoFstObj f α p) (Implementation.smulIsoSndObj f α p)
    (Implementation.smulIsoApp_fst_isHomLift f α p) (Implementation.smulIsoApp_snd_isHomLift f α p)
    (Implementation.smulIsoApp_comm f α p)

/-- The comparison of postcomposition with the prescribed fibre is natural. -/
private theorem Implementation.smulIso_naturality {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    {p q : (smulApex f α).total} (g : p ⟶ q) :
    (toFunctor (Implementation.smulToPair f α ≫ pairComparison f x1 x2)).map g ≫
        (Implementation.smulIsoApp f α q).hom =
      (Implementation.smulIsoApp f α p).hom ≫
        (toFunctor (smulStructure f α ≫ diagonalAlpha α)).map g :=
  sorry

/-- The comparison of postcomposition with the prescribed fibre is vertical. -/
private theorem Implementation.smulIso_isHomLift {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f)
    (p : (smulApex f α).total) :
    (FiberedCategoryOver.Groupoids.p
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} (x1 ≫ f) (x2 ≫ f))).IsHomLift
      (𝟙 ((smulApex f α).p.obj p)) (Implementation.smulIsoApp f α p).hom :=
  sorry

/-- The 2-isomorphism witnessing that postcomposition equalizes `pairComparison`
against `diagonalAlpha`, using that the automorphism factor maps to the identity
in `Y`. -/
private def Implementation.smulIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Implementation.smulToPair f α ≫ pairComparison f x1 x2 ≅
      smulStructure f α ≫ diagonalAlpha α :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (Implementation.smulIsoApp f α)
      (fun g ↦ Implementation.smulIso_naturality f α g) (Implementation.smulIso_isHomLift f α))

/-- The postcomposition cone of relative isomorphisms over `Z`. -/
private def Implementation.smulCone {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Bicategory.PseudoPullbackCone (pairComparison f x1 x2) (diagonalAlpha α) where
  pt := smulApex f α
  fst := Implementation.smulToPair f α
  snd := smulStructure f α
  iso := Implementation.smulIso f α

/-- Postcomposition
`(Z ×_X I_{X/Y}) ×_Z Isom^α_{X/Y}(x1, x2) ⟶ Isom^α_{X/Y}(x1, x2)`. -/
def smulMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulApex f α ⟶ relativeIsom f α :=
  Bicategory.PseudoPullbackCone.lift (Implementation.smulCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (pairComparison f x1 x2) (diagonalAlpha α))

/-- Postcomposition followed by the comparison into the pair product `Z ×_X Z` recovers
the composition of fibre isomorphisms. -/
private def Implementation.smulMap_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulMap f α ≫ relativeIsom.fst f α ≅ Implementation.smulToPair f α :=
  Bicategory.PseudoPullbackCone.lift.fstIso (Implementation.smulCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (pairComparison f x1 x2) (diagonalAlpha α))

/-- Postcomposition followed by the structure map to `Z` recovers the structure
morphism of the binary product over `Z`. -/
def smulMap_snd {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    smulMap f α ≫ relativeIsom.snd f α ≅ smulStructure f α :=
  Bicategory.PseudoPullbackCone.lift.sndIso (Implementation.smulCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (pairComparison f x1 x2) (diagonalAlpha α))

/-- The action 1-morphism of relative automorphisms on relative isomorphisms in
`SpacesOver Z.toGroupoids`. -/
def smulHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    tensor (asSpacesOver f x2) (asSpacesOverIsom f α) ⟶ asSpacesOverIsom f α :=
  SpacesOver.homMk (smulMap f α) (smulMap_snd f α).symm

/-- The underlying domain map of `smulHom f α` is `smulMap f α`. -/
theorem smulHom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    SpacesOver.map (smulHom f α) = smulMap f α :=
  rfl

/-- The identity relative automorphism acts as the identity. -/
private theorem Implementation.action_one_smul {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    (MonoidalCategory.whiskerRight η[asHomotopy f x2] (asHomotopyIsom f α)) ≫
        Bicategory.HomotopyCategory.mkHom (smulHom f α) =
      (MonoidalCategory.leftUnitor (asHomotopyIsom f α)).hom :=
  sorry

/-- Composition of relative automorphisms is compatible with postcomposition. -/
private theorem Implementation.action_mul_smul {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    (MonoidalCategory.whiskerRight μ[asHomotopy f x2] (asHomotopyIsom f α)) ≫
        Bicategory.HomotopyCategory.mkHom (smulHom f α) =
      (MonoidalCategory.associator (asHomotopy f x2) (asHomotopy f x2) (asHomotopyIsom f α)).hom ≫
        (MonoidalCategory.whiskerLeft (asHomotopy f x2) (Bicategory.HomotopyCategory.mkHom (smulHom f α))) ≫
          Bicategory.HomotopyCategory.mkHom (smulHom f α) :=
  sorry

/-- The canonical module-object structure of `Isom_{X/Y}(x2, x2)` on
`Isom^α_{X/Y}(x1, x2)`. -/
instance instModObj_relativeIsom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    ModObj (asHomotopy f x2) (asHomotopyIsom f α) where
  smul := Bicategory.HomotopyCategory.mkHom (smulHom f α)
  one_smul := Implementation.action_one_smul f α
  mul_smul := Implementation.action_mul_smul f α

/-- The action of `Isom_{X/Y}(x2, x2)` on `Isom^α_{X/Y}(x1, x2)` over `Z`. -/
def action {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Mod (Bicategory.HomotopyCategory (SpacesOver Z.toGroupoids))
      (asHomotopy f x2) where
  X := asHomotopyIsom f α

/-- The underlying object of `action f α` is `asHomotopyIsom f α`. -/
theorem action_X {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    (action f α).X = asHomotopyIsom f α :=
  rfl

/-- `Isom^α_{X/Y}(x1, x2)` is a pseudo-torsor for `Isom_{X/Y}(x2, x2)` over `Z`. -/
instance instIsPseudoTorsor_action {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    Mod.IsPseudoTorsor (action f α) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
