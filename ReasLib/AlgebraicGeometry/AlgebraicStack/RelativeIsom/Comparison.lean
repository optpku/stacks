/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable.Naturality
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Projections
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Group
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Construction

/-!
# Kernel and comparison maps of relative automorphism sheaves

For a morphism `f : X ⟶ Y` of algebraic stacks and a morphism `x : Z ⟶ X`
from an algebraic space, the relative automorphism sheaf sits in a left-exact
sequence of group objects
`Isom_{X/Y}(x, x) ⟶ Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` in the homotopy
category of algebraic spaces over `Z`. The relative isomorphism sheaf is the
apex of the 2-fibre product of `pairComparison` against `diagonalAlpha`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.RelativeInertia
open scoped Bicategory CategoryTheory.MonObj Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

/-- The invertible square sending relative inertia of `f` to relative inertia
of the base projection of `X`. -/
private def Implementation.kernelSquareIso {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    f ≫ baseProjection.{u + 1, u, u + 1} Y ≅
      𝟙 X ≫ baseProjection.{u + 1, u, u + 1} X :=
  eqToIso (comp_baseProjection f) ≪≫
    (λ_ (baseProjection.{u + 1, u, u + 1} X)).symm

/-- The cospan transformation presenting the kernel inclusion
`Z ×_X I_{X/Y} ⟶ Z ×_X I_X`. -/
private def Implementation.kernelCospan {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    CospanTransform x (forget.{u + 1, u, u, u + 1} f) x
      (forget.{u + 1, u, u, u + 1}
        (baseProjection.{u + 1, u, u + 1} X)) :=
  CospanTransform.mk (𝟙 Z.toGroupoids)
    (RelativeInertia.map.{u + 1, u, u, u + 1} (𝟙 X)
      (baseProjection.{u + 1, u, u + 1} Y) (Implementation.kernelSquareIso f))
    (𝟙 X) (λ_ x ≪≫ (ρ_ x).symm)
    (eqToIso
      (RelativeInertia.map.comp_forget.{u + 1, u, u, u + 1} (𝟙 X)
        (baseProjection.{u + 1, u, u + 1} Y) (Implementation.kernelSquareIso f)))

/-- The kernel inclusion `Isom_{X/Y}(x, x) ⟶ Isom_X(x, x)` as a 1-morphism of
groupoid fibrations. -/
def kernelιMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    relativeAut f x ⟶ relativeAut (baseProjection.{u + 1, u, u + 1} X) x :=
  TwoFibreProduct.map (Implementation.kernelCospan f x)

/-- The kernel inclusion followed by the structure map of `Isom_X(x, x)` recovers
the structure map of `Isom_{X/Y}(x, x)`. -/
def kernelιMap_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    kernelιMap f x ≫ fst (baseProjection.{u + 1, u, u + 1} X) x ≅ fst f x :=
  TwoFibreProduct.map.fstIso (Implementation.kernelCospan f x) ≪≫ ρ_ (fst f x)

/-- The kernel inclusion as a 1-morphism of `SpacesOver Z.toGroupoids`. -/
def kernelιHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asSpacesOver f x ⟶
      asSpacesOver (baseProjection.{u + 1, u, u + 1} X) x :=
  SpacesOver.homMk (kernelιMap f x) (kernelιMap_fst f x).symm

/-- The underlying domain map of `kernelιHom f x` is `kernelιMap f x`. -/
theorem kernelιHom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    SpacesOver.map (kernelιHom f x) = kernelιMap f x :=
  rfl

/-- The kernel inclusion of relative automorphisms in the homotopy category of
algebraic spaces over `Z`. -/
def kernelι {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asHomotopy f x ⟶ asHomotopy (baseProjection.{u + 1, u, u + 1} X) x :=
  Bicategory.HomotopyCategory.mkHom (kernelιHom f x)

/-- The invertible square sending relative inertia of the base projection of `X`
to relative inertia of the base projection of `Y`. -/
private def Implementation.toTargetSquareIso {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    baseProjection.{u + 1, u, u + 1} X ≫
        𝟙 (FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S)) ≅
      f ≫ baseProjection.{u + 1, u, u + 1} Y :=
  ρ_ (baseProjection.{u + 1, u, u + 1} X) ≪≫
    eqToIso (comp_baseProjection f).symm

/-- The cospan transformation presenting
`Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)`. -/
private def Implementation.toTargetCospan {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    CospanTransform x
      (forget.{u + 1, u, u, u + 1} (baseProjection.{u + 1, u, u + 1} X))
      (x ≫ f)
      (forget.{u + 1, u, u, u + 1} (baseProjection.{u + 1, u, u + 1} Y)) :=
  CospanTransform.mk (𝟙 Z.toGroupoids)
    (RelativeInertia.map.{u + 1, u, u, u + 1} f
      (𝟙 (FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S))) (Implementation.toTargetSquareIso f))
    f (λ_ (x ≫ f))
    (eqToIso
      (RelativeInertia.map.comp_forget.{u + 1, u, u, u + 1} f
        (𝟙 (FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S))) (Implementation.toTargetSquareIso f)))

/-- The comparison `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` as a 1-morphism of
groupoid fibrations. -/
def toTargetMap {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    relativeAut (baseProjection.{u + 1, u, u + 1} X) x ⟶
      relativeAut (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  TwoFibreProduct.map (Implementation.toTargetCospan f x)

/-- `toTargetMap` commutes with structure maps to `Z` up to the identity unitor. -/
def toTargetMap_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    toTargetMap f x ≫ fst (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) ≅
      fst (baseProjection.{u + 1, u, u + 1} X) x :=
  TwoFibreProduct.map.fstIso (Implementation.toTargetCospan f x) ≪≫
    ρ_ (fst (baseProjection.{u + 1, u, u + 1} X) x)

/-- The comparison `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` as a 1-morphism of
`SpacesOver Z.toGroupoids`. -/
def toTargetHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asSpacesOver (baseProjection.{u + 1, u, u + 1} X) x ⟶
      asSpacesOver (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  SpacesOver.homMk (toTargetMap f x) (toTargetMap_fst f x).symm

/-- The underlying domain map of `toTargetHom f x` is `toTargetMap f x`. -/
theorem toTargetHom_left {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    SpacesOver.map (toTargetHom f x) = toTargetMap f x :=
  rfl

/-- The comparison `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` in the homotopy
category of algebraic spaces over `Z`. -/
def toTarget {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asHomotopy (baseProjection.{u + 1, u, u + 1} X) x ⟶
      asHomotopy (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  Bicategory.HomotopyCategory.mkHom (toTargetHom f x)

/-- The trivial homomorphism `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` through the
unit section of the target. -/
def constOneHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asSpacesOver (baseProjection.{u + 1, u, u + 1} X) x ⟶
      asSpacesOver (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  SpacesOver.toId (asSpacesOver (baseProjection.{u + 1, u, u + 1} X) x) ≫
    oneHom (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f)

/-- The trivial homomorphism `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` in the
homotopy category of algebraic spaces over `Z`. -/
def constOne {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    asHomotopy (baseProjection.{u + 1, u, u + 1} X) x ⟶
      asHomotopy (baseProjection.{u + 1, u, u + 1} Y) (x ≫ f) :=
  Bicategory.HomotopyCategory.mkHom (constOneHom f x)

/-- The kernel inclusion equalizes `toTarget` and the trivial homomorphism. -/
theorem kernelι_comp_toTarget {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    kernelι f x ≫ toTarget f x = kernelι f x ≫ constOne f x :=
  sorry

/-- The kernel inclusion is a homomorphism of group objects. -/
instance instIsMonHom_kernelι {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    IsMonHom (kernelι f x) :=
  sorry

/-- The comparison `Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` is a homomorphism of
group objects. -/
instance instIsMonHom_toTarget {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X) :
    IsMonHom (toTarget f x) :=
  sorry

/-- The relative automorphism sheaf is the kernel of
`Isom_X(x, x) ⟶ Isom_Y(f ∘ x, f ∘ x)` at the identity section. -/
theorem isomExactSequence {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {Z : AlgebraicSpace S} (x : Z.toGroupoids ⟶ X)
    {G : Bicategory.HomotopyCategory (SpacesOver Z.toGroupoids)}
    (φ : G ⟶ asHomotopy (baseProjection.{u + 1, u, u + 1} X) x) :
    (∃! ψ : G ⟶ asHomotopy f x, ψ ≫ kernelι f x = φ) ↔
      φ ≫ toTarget f x = φ ≫ constOne f x :=
  sorry

/-- The projection of relative isomorphisms to the pair product `Z ×_X Z`. -/
def relativeIsom.fst {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom f α ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2 :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u}
    (pairComparison f x1 x2) (diagonalAlpha α)

/-- The structure morphism `Isom^α_{X/Y}(x1, x2) ⟶ Z`. -/
def relativeIsom.snd {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom f α ⟶ Z.toGroupoids :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u}
    (pairComparison f x1 x2) (diagonalAlpha α)

/-- The first `Z`-leg of the pair product `Z ×_X Z` recovers the structure map of
`Isom^α_{X/Y}(x1, x2)`. -/
def relativeIsom.fst_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom.fst f α ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} x1 x2 ≅
      relativeIsom.snd f α :=
  whiskerLeftIso (relativeIsom.fst f α) (ρ_ _).symm ≪≫
    whiskerLeftIso (relativeIsom.fst f α)
        (TwoFibreProduct.map.fstIso (pairComparisonCospan f x1 x2)).symm ≪≫
      (α_ _ _ _).symm ≪≫
        whiskerRightIso
            (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u}
              (pairComparison f x1 x2) (diagonalAlpha α))
            (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (x1 ≫ f)
              (x2 ≫ f)) ≪≫
          α_ _ _ _ ≪≫
            whiskerLeftIso (relativeIsom.snd f α) (diagonalAlpha_fst α) ≪≫
              ρ_ _

/-- The second `Z`-leg of the pair product `Z ×_X Z` recovers the structure map of
`Isom^α_{X/Y}(x1, x2)`. -/
def relativeIsom.fst_snd {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom.fst f α ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} x1 x2 ≅
      relativeIsom.snd f α :=
  whiskerLeftIso (relativeIsom.fst f α) (ρ_ _).symm ≪≫
    whiskerLeftIso (relativeIsom.fst f α)
        (TwoFibreProduct.map.sndIso (pairComparisonCospan f x1 x2)).symm ≪≫
      (α_ _ _ _).symm ≪≫
        whiskerRightIso
            (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u}
              (pairComparison f x1 x2) (diagonalAlpha α))
            (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (x1 ≫ f)
              (x2 ≫ f)) ≪≫
          α_ _ _ _ ≪≫
            whiskerLeftIso (relativeIsom.snd f α) (diagonalAlpha_snd α) ≪≫
              ρ_ _

/-- The isomorphism `x1 ≅ x2` carried by `Isom^α_{X/Y}(x1, x2)` over `Z`. -/
def relativeIsom.compIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom.snd f α ≫ x1 ≅ relativeIsom.snd f α ≫ x2 :=
  whiskerRightIso (relativeIsom.fst_fst f α).symm x1 ≪≫
    α_ _ _ _ ≪≫
      whiskerLeftIso (relativeIsom.fst f α)
          (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} x1 x2) ≪≫
        (α_ _ _ _).symm ≪≫
          whiskerRightIso (relativeIsom.fst_snd f α) x2


/-- Parallel vertical transformations into a faithful fibration are equal. -/
private theorem Implementation.twoCell_ext {S : Scheme.{u}} {A W : GroupoidsOver S}
    (hW : W.p.Faithful) {F G : A ⟶ W} (a b : F ⟶ G) : a = b := by
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext p
  apply hW.map_injective
  rw [IsHomLift.fac' W.p (𝟙 (A.p.obj p)) ((toNatTrans a).app p),
    IsHomLift.fac' W.p (𝟙 (A.p.obj p)) ((toNatTrans b).app p)]

/-- The common-base projection of a product of faithful fibrations is faithful. -/
private theorem Implementation.pullbackFaithful {S : Scheme.{u}}
    {L R W : GroupoidsOver S} (l : L ⟶ W) (r : R ⟶ W)
    (hL : L.p.Faithful) (hR : R.p.Faithful) :
    (FiberedCategoryOver.Groupoids.p
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} l r)).Faithful where
  map_injective := by
    intro P Q a b hab
    apply BasedCategory.PseudoPullback.hom_ext
    · apply hL.map_injective
      rw [IsHomLift.fac' L.p (BasedCategory.PseudoPullback.baseMap a),
        IsHomLift.fac' L.p (BasedCategory.PseudoPullback.baseMap b)]
      exact congrArg (fun k => _ ≫ k ≫ _) hab
    · apply hR.map_injective
      rw [IsHomLift.fac' R.p (BasedCategory.PseudoPullback.baseMap a),
        IsHomLift.fac' R.p (BasedCategory.PseudoPullback.baseMap b)]
      exact congrArg (fun k => _ ≫ k ≫ _) hab

/-- Compatible projection isomorphisms determine an isomorphism into a pullback
whose central target has faithful projection. -/
private def Implementation.pullbackIso {S : Scheme.{u}} {A L R W : GroupoidsOver S}
    {l : L ⟶ W} {r : R ⟶ W} (hW : W.p.Faithful)
    (F G : A ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} l r)
    (eL : F ≫ TwoFibreProduct.fst l r ≅ G ≫ TwoFibreProduct.fst l r)
    (eR : F ≫ TwoFibreProduct.snd l r ≅ G ≫ TwoFibreProduct.snd l r) : F ≅ G := by
  let c := (TwoFibreProduct.cone.{u + 1, u, u + 1, u} l r).toPseudoCone.comparison A
  apply (Functor.FullyFaithful.ofFullyFaithful c).preimageIso
  refine Pseudofunctor.StrongTrans.isoMk (fun j => ?_) ?_
  · cases j with
    | mk j =>
      cases j with
      | none => exact whiskerRightIso eL l
      | some j =>
        cases j with
        | left => exact eL
        | right => exact eR
  · intro a b h
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases h with ⟨h⟩
    cases h with
    | id a =>
        change _ ◁ _ ≫ ((c.obj G).naturality (𝟙 (LocallyDiscrete.mk a))).hom =
          ((c.obj F).naturality (𝟙 (LocallyDiscrete.mk a))).hom ≫ _ ▷ _
        rw [Pseudofunctor.StrongTrans.naturality_id_hom,
          Pseudofunctor.StrongTrans.naturality_id_hom]
        change (𝟙 A ◁ _) ≫ (𝟙 _ ▷ _) ≫ (λ_ _).hom ≫ (ρ_ _).inv ≫ (_ ◁ 𝟙 _) =
          ((𝟙 _ ▷ _) ≫ (λ_ _).hom ≫ (ρ_ _).inv ≫ (_ ◁ 𝟙 _)) ≫ (_ ▷ 𝟙 _)
        simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
        simp only [id_whiskerLeft, whiskerRight_id, Category.assoc,
          Iso.inv_hom_id_assoc]
    | term j => exact Implementation.twoCell_ext hW _ _

/-- Two identified legs into an algebraic space identify a map to its product
with the diagonal of their common value. -/
private def Implementation.toSelfIso {S : Scheme.{u}} {A X : GroupoidsOver S}
    {Z : AlgebraicSpace S} (x1 x2 : Z.toGroupoids ⟶ X)
    (a : A ⟶ Z.toGroupoids)
    (b : A ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2)
    (e1 : b ≫ TwoFibreProduct.fst x1 x2 ≅ a)
    (e2 : b ≫ TwoFibreProduct.snd x1 x2 ≅ a) :
    a ≫ diagonal.{u + 1, u, u + 1} Z.toGroupoids ≅ b ≫ toSelfProduct x1 x2 :=
  Implementation.pullbackIso
    (Functor.IsDiscreteFibration.faithful (Cat.ObjULift.down.{u + 1, u, u + 1} (Over S))) _ _
    ((α_ _ _ _ ≪≫ whiskerLeftIso a (Hom.diagonal.fstIso _) ≪≫ ρ_ a) ≪≫
      (α_ _ _ _ ≪≫
        whiskerLeftIso b (TwoFibreProduct.map.fstIso (toSelfCospan x1 x2)) ≪≫
        whiskerLeftIso b (ρ_ _) ≪≫ e1).symm)
    ((α_ _ _ _ ≪≫ whiskerLeftIso a (Hom.diagonal.sndIso _) ≪≫ ρ_ a) ≪≫
      (α_ _ _ _ ≪≫
        whiskerLeftIso b (TwoFibreProduct.map.sndIso (toSelfCospan x1 x2)) ≪≫
        whiskerLeftIso b (ρ_ _) ≪≫ e2).symm)

/-- A prescribed isomorphism determines a cone over the diagonal of its common base. -/
private def Implementation.comparisonSectionCone {S : Scheme.{u}} {Y : GroupoidsOver S}
    {Z : AlgebraicSpace S} {y1 y2 : Z.toGroupoids ⟶ Y} (α : y1 ≅ y2) :
    PseudoPullbackCone (diagonal.{u + 1, u, u + 1} Z.toGroupoids)
      (toSelfProduct y1 y2) where
  pt := Z.toGroupoids
  fst := 𝟙 Z.toGroupoids
  snd := diagonalAlpha α
  iso := Implementation.toSelfIso y1 y2 (𝟙 Z.toGroupoids) (diagonalAlpha α)
    (diagonalAlpha_fst α) (diagonalAlpha_snd α)

/-- A prescribed isomorphism gives a section of the same-base Isom object. -/
def comparisonSection {S : Scheme.{u}} {Y : GroupoidsOver S}
    {Z : AlgebraicSpace S} {y1 y2 : Z.toGroupoids ⟶ Y} (α : y1 ≅ y2) :
    Z.toGroupoids ⟶ AlgebraicStack.isomApex y1 y2 :=
  PseudoPullbackCone.lift (Implementation.comparisonSectionCone α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (diagonal.{u + 1, u, u + 1} Z.toGroupoids) (toSelfProduct y1 y2))

/-- The two legs of a relative isomorphism determine a cone over the common-base diagonal. -/
private def Implementation.toIsomCone {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    PseudoPullbackCone (diagonal.{u + 1, u, u + 1} Z.toGroupoids)
      (toSelfProduct x1 x2) where
  pt := relativeIsom f α
  fst := relativeIsom.snd f α
  snd := relativeIsom.fst f α
  iso := Implementation.toSelfIso x1 x2 (relativeIsom.snd f α) (relativeIsom.fst f α)
    (relativeIsom.fst_fst f α) (relativeIsom.fst_snd f α)

/-- Forget the prescribed image of a relative isomorphism, retaining its common base point. -/
def relativeIsom.toIsom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom f α ⟶ AlgebraicStack.isomApex x1 x2 :=
  PseudoPullbackCone.lift (Implementation.toIsomCone f α)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (diagonal.{u + 1, u, u + 1} Z.toGroupoids) (toSelfProduct x1 x2))

/-- The image of a relative isomorphism in the target Isom object is its prescribed section. -/
def comparisonIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    relativeIsom.toIsom f α ≫ AlgebraicStack.isomComparison f x1 x2 ≅
      relativeIsom.snd f α ≫ comparisonSection α := by
  apply Implementation.pullbackIso
    (Implementation.pullbackFaithful _ _
      (Functor.IsDiscreteFibration.faithful
        ((FiberedCategoryOver.Sets.ofPresheaf (Over S)).obj Z.functorOfPoints).p)
      (Functor.IsDiscreteFibration.faithful
        ((FiberedCategoryOver.Sets.ofPresheaf (Over S)).obj Z.functorOfPoints).p))
  · exact
      (α_ _ _ _ ≪≫
        whiskerLeftIso (relativeIsom.toIsom f α)
          (TwoFibreProduct.map.fstIso (isomCospan f x1 x2)) ≪≫
        whiskerLeftIso (relativeIsom.toIsom f α) (ρ_ _) ≪≫
        PseudoPullbackCone.lift.fstIso (Implementation.toIsomCone f α) _) ≪≫
      (α_ _ _ _ ≪≫
        whiskerLeftIso (relativeIsom.snd f α)
          (PseudoPullbackCone.lift.fstIso (Implementation.comparisonSectionCone α) _) ≪≫
        ρ_ _).symm
  · exact
      (α_ _ _ _ ≪≫
        whiskerLeftIso (relativeIsom.toIsom f α)
          (TwoFibreProduct.map.sndIso (isomCospan f x1 x2)) ≪≫
        (α_ _ _ _).symm ≪≫
        whiskerRightIso
          (PseudoPullbackCone.lift.sndIso (Implementation.toIsomCone f α) _)
          (pairComparison f x1 x2)) ≪≫
      TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u}
        (pairComparison f x1 x2) (diagonalAlpha α) ≪≫
      (α_ _ _ _ ≪≫
        whiskerLeftIso (relativeIsom.snd f α)
          (PseudoPullbackCone.lift.sndIso (Implementation.comparisonSectionCone α) _)).symm

/-- The square comparing relative isomorphisms with the fibre of the same-base Isom map. -/
def comparisonCone {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {Z : AlgebraicSpace S} {x1 x2 : Z.toGroupoids ⟶ X}
    (α : x1 ≫ f ≅ x2 ≫ f) :
    PseudoPullbackCone (AlgebraicStack.isomComparison f x1 x2) (comparisonSection α) where
  pt := relativeIsom f α
  fst := relativeIsom.toIsom f α
  snd := relativeIsom.snd f α
  iso := comparisonIso f α

/-- Relative isomorphisms are the cartesian fibre of the same-base Isom comparison
above the section defined by the prescribed image. -/
theorem comparisonCone_isBilimit {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    {x1 x2 : Z.toGroupoids ⟶ X} (α : x1 ≫ f ≅ x2 ≫ f) :
    (comparisonCone f α).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
