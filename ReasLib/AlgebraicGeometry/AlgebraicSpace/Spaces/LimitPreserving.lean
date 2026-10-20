/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Groupoids
public import ReasLib.CategoryTheory.Fibered.Fiber.Restriction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects

/-!
# Limit preservation for finite-presentation, flat, proper algebraic spaces

Over directed inverse limits of affine schemes, finite-presentation, flat, proper
algebraic spaces descend up to isomorphism, and their fibre Hom-types are colimits
of the canonical stage Hom-diagrams in `Type (u + 1)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
open TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids

variable (S : Scheme.{u})

/-- Iterated restriction along successive bonding maps of a directed inverse
system agrees with restriction along the composite bonding map. -/
def restrictObj_stage {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i i' i'' : I} (x : (pFpFlatProperGroupoids S).Fiber (D.obj i))
    (hi : i ≤ i') (hi' : i' ≤ i'') (hii : i ≤ i'') :
    restrictObj (restrictObj x (stageHom hi)) (stageHom hi') ≅
      restrictObj x (stageHom hii) :=
  restrictObj_comp x (stageHom hi) (stageHom hi') ≪≫
    restrictObj_eq x
      ((D.map_comp (homOfLE (OrderDual.toDual_le_toDual.mpr hi'))
          (homOfLE (OrderDual.toDual_le_toDual.mpr hi))).symm.trans
        (congrArg D.map (Subsingleton.elim _ _)))

/-- The forward map of `restrictObj_stage` is the composite of `restrictObj_comp`
with the identification of the composite bonding map. -/
theorem restrictObj_stage_hom {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i i' i'' : I} (x : (pFpFlatProperGroupoids S).Fiber (D.obj i))
    (hi : i ≤ i') (hi' : i' ≤ i'') (hii : i ≤ i'') :
    (restrictObj_stage S x hi hi' hii).hom =
      (restrictObj_comp x (stageHom hi) (stageHom hi')).hom ≫
        (restrictObj_eq x
          ((D.map_comp (homOfLE (OrderDual.toDual_le_toDual.mpr hi'))
              (homOfLE (OrderDual.toDual_le_toDual.mpr hi))).symm.trans
            (congrArg D.map (Subsingleton.elim _ _)))).hom :=
  rfl

/-- Restriction of a stage fibre object to the cone point agrees with restriction
along the cone projection of that stage. -/
def restrictObj_cone {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i i' : I} (c : Cone D) (x : (pFpFlatProperGroupoids S).Fiber (D.obj i))
    (hi : i ≤ i') :
    restrictObj (restrictObj x (stageHom hi)) (c.π.app i') ≅
      restrictObj x (c.π.app i) :=
  restrictObj_comp x (stageHom hi) (c.π.app i') ≪≫
    restrictObj_eq x (Cone.w c (homOfLE (OrderDual.toDual_le_toDual.mpr hi)))

/-- The forward map of `restrictObj_cone` is the composite of `restrictObj_comp`
with the cone-compatibility identification. -/
theorem restrictObj_cone_hom {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i i' : I} (c : Cone D) (x : (pFpFlatProperGroupoids S).Fiber (D.obj i))
    (hi : i ≤ i') :
    (restrictObj_cone S c x hi).hom =
      (restrictObj_comp x (stageHom hi) (c.π.app i')).hom ≫
        (restrictObj_eq x
          (Cone.w c (homOfLE (OrderDual.toDual_le_toDual.mpr hi)))).hom :=
  rfl

/-- The transition map of fibre Hom-types along a later bonding map of the inverse
system. -/
def restrictHomAlongStage {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i : I} (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i))
    {j j' : Set.Ici i} (h : j ⟶ j')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictObj x (stageHom j'.2) ⟶ restrictObj y (stageHom j'.2) :=
  (restrictObj_stage S x j.2 (leOfHom h) j'.2).inv ≫
    restrictHom φ (stageHom (leOfHom h)) ≫
    (restrictObj_stage S y j.2 (leOfHom h) j'.2).hom

/-- `restrictHomAlongStage` transports a fibre morphism by restriction along the
bonding map and the iterated-restriction comparison. -/
theorem restrictHomAlongStage_apply {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i : I}
    (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)) {j j' : Set.Ici i}
    (h : j ⟶ j')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomAlongStage S x y h φ =
      (restrictObj_stage S x j.2 (leOfHom h) j'.2).inv ≫
        restrictHom φ (stageHom (leOfHom h)) ≫
        (restrictObj_stage S y j.2 (leOfHom h) j'.2).hom :=
  rfl

/-- Transition along an identity stage map fixes every fibre morphism. -/
theorem restrictHomAlongStage_id {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i : I}
    (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)) (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomAlongStage S x y (𝟙 j) φ = φ :=
  sorry

/-- Transition along a composite stage map is the composite of the transitions. -/
theorem restrictHomAlongStage_comp {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i : I}
    (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i))
    {j j' j'' : Set.Ici i} (h : j ⟶ j') (h' : j' ⟶ j'')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomAlongStage S x y (h ≫ h') φ =
      restrictHomAlongStage S x y h' (restrictHomAlongStage S x y h φ) :=
  sorry

/-- The directed diagram of fibre Hom-types of restrictions of a stage pair along
bonding maps. -/
def homFunctor {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} {i : I}
    (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)) :
    Set.Ici i ⥤ Type (u + 1) where
  obj j := restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)
  map h := TypeCat.ofHom.{u + 1} (restrictHomAlongStage S x y h)
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact restrictHomAlongStage_id S x y j φ
  map_comp h h' := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact restrictHomAlongStage_comp S x y h h' φ

/-- The object map of `homFunctor` is the fibre Hom-type after restriction along
the bonding map of that stage. -/
theorem homFunctor_obj {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i : I} (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)) (j : Set.Ici i) :
    (homFunctor S x y).obj j =
      (restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :=
  rfl

/-- The cocone leg sending a later-stage fibre morphism to its restriction along
the cone projection. -/
def restrictHomToLimit {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i : I} (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i))
    (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i) :=
  (restrictObj_cone S c x j.2).inv ≫
    restrictHom φ (c.π.app j.1) ≫ (restrictObj_cone S c y j.2).hom

/-- `restrictHomToLimit` is restriction along the cone projection, transported by
`restrictObj_cone`. -/
theorem restrictHomToLimit_apply {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I}
    (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)) (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomToLimit S c x y j φ =
      (restrictObj_cone S c x j.2).inv ≫
        restrictHom φ (c.π.app j.1) ≫ (restrictObj_cone S c y j.2).hom :=
  rfl

/-- Restriction to the cone point commutes with transition to a later stage. -/
theorem restrictHomToLimit_naturality {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I}
    (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i))
    {j j' : Set.Ici i} (h : j ⟶ j')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomToLimit S c x y j' (restrictHomAlongStage S x y h φ) =
      restrictHomToLimit S c x y j φ :=
  sorry

/-- The canonical cocone from the directed Hom-diagram of a stage pair to the
fibre Hom-type over the cone point. -/
def homCocone {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} (c : Cone D)
    {i : I} (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)) :
    Cocone (homFunctor S x y) where
  pt := restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i)
  ι :=
    { app := fun j ↦ TypeCat.ofHom.{u + 1} (restrictHomToLimit S c x y j)
      naturality := by
        intro j j' h
        apply ConcreteCategory.hom_ext
        intro φ
        exact restrictHomToLimit_naturality S c x y h φ }

/-- The vertex of `homCocone` is the fibre Hom-type of the restrictions of `x`
and `y` to the cone point. -/
theorem homCocone_pt {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i : I} (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)) :
    (homCocone S c x y).pt =
      (restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i)) :=
  rfl

/-- The components of `homCocone.ι` are `restrictHomToLimit`. -/
theorem homCocone_ι_app {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i : I} (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i))
    (j : Set.Ici i) :
    (homCocone S c x y).ι.app j =
      TypeCat.ofHom.{u + 1} (restrictHomToLimit S c x y j) :=
  rfl

/-- Object descent for `pFpFlatProperGroupoids S` along directed inverse limits
of affine schemes over `S`. -/
theorem exists_stage (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (x : (pFpFlatProperGroupoids S).Fiber c.pt) :
    ∃ (i : I) (xi : (pFpFlatProperGroupoids S).Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x :=
  sorry

/-- Fibre Hom-types of `pFpFlatProperGroupoids S` over a directed inverse limit
of affine schemes over `S` are the directed colimit of the corresponding stage
Hom-types. -/
theorem hom_isColimit (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (i : I) (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)) :
    Nonempty (IsColimit (homCocone S c x y)) :=
  sorry

/-- Finite-presentation, flat, proper algebraic spaces form a limit-preserving
category fibred in groupoids: objects descend up to isomorphism along directed
affine inverse limits, and the canonical fibre Hom-cocones are colimit cocones. -/
theorem isLimitPreserving (S : Scheme.{u})
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left) :
    (∀ x : (pFpFlatProperGroupoids S).Fiber c.pt,
      ∃ (i : I) (xi : (pFpFlatProperGroupoids S).Fiber (D.obj i)),
        IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
      ∀ (i : I) (x y : (pFpFlatProperGroupoids S).Fiber (D.obj i)),
        Nonempty (IsColimit (homCocone S c x y)) :=
  ⟨exists_stage S D c hc hD hpt, hom_isColimit S D c hc hD hpt⟩

end AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
