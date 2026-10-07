module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap99.Situation_99_5_1

/-!
# The stack of coherent sheaves as a category fibred in groupoids

Situation 99.5.1 supplies the total category `CohStack.Obj f` and the projection
`p : Obj f ⥤ Over S`. Hom-types of `Obj f` live in `Type (u + 1)` because they
include morphisms of module sheaves on the large étale site, so the bundled
projection cannot inhabit `GroupoidsOver S` (which pins Hom-universe `u`). The
packaging below matches `FtGroupoids.toGroupoids`, and the Artin Hom-colimit
diagram is built at `Type (u + 1)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
open TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The projection `p : Obj f ⥤ Over S` is fibred in groupoids. -/
instance instIsFiberedInGroupoids (f : X ⟶ B) [FinitePresentation f] :
    Functor.IsFibered.InGroupoids (p f) :=
  sorry

/-- The category of finitely presented quasi-coherent modules with proper
support on the fibres of `f`, bundled as a category fibred in groupoids over
`Over S`. The Hom-universe is `u + 1`, so this cannot land in `GroupoidsOver S`. -/
def toGroupoids (f : X ⟶ B) [FinitePresentation f] :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u + 1} (p f)

/-- The projection of `toGroupoids f` is the source functor `p f`, sending
`(T, g, F)` to `T`. -/
theorem toGroupoids_p (f : X ⟶ B) [FinitePresentation f] :
    (toGroupoids f).p = p f :=
  sorry

/-- The total category of `toGroupoids f` is the category `Obj f` of
Situation 99.5.1. -/
theorem toGroupoids_total (f : X ⟶ B) [FinitePresentation f] :
    (toGroupoids f).total = Obj f :=
  sorry

variable (f : X ⟶ B) [FinitePresentation f]

/-- Iterated restriction along successive bonding maps of a directed inverse
system agrees with restriction along the composite bonding map. -/
def restrictObj_stage {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i i' i'' : I} (x : (p f).Fiber (D.obj i))
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
    {i i' i'' : I} (x : (p f).Fiber (D.obj i))
    (hi : i ≤ i') (hi' : i' ≤ i'') (hii : i ≤ i'') :
    (restrictObj_stage f x hi hi' hii).hom =
      (restrictObj_comp x (stageHom hi) (stageHom hi')).hom ≫
        (restrictObj_eq x
          ((D.map_comp (homOfLE (OrderDual.toDual_le_toDual.mpr hi'))
              (homOfLE (OrderDual.toDual_le_toDual.mpr hi))).symm.trans
            (congrArg D.map (Subsingleton.elim _ _)))).hom :=
  sorry

/-- Restriction of a stage fibre object to the cone point agrees with restriction
along the cone projection of that stage. -/
def restrictObj_cone {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i i' : I} (c : Cone D) (x : (p f).Fiber (D.obj i)) (hi : i ≤ i') :
    restrictObj (restrictObj x (stageHom hi)) (c.π.app i') ≅
      restrictObj x (c.π.app i) :=
  restrictObj_comp x (stageHom hi) (c.π.app i') ≪≫
    restrictObj_eq x (Cone.w c (homOfLE (OrderDual.toDual_le_toDual.mpr hi)))

/-- The forward map of `restrictObj_cone` is the composite of `restrictObj_comp`
with the cone-compatibility identification. -/
theorem restrictObj_cone_hom {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i i' : I} (c : Cone D) (x : (p f).Fiber (D.obj i)) (hi : i ≤ i') :
    (restrictObj_cone f c x hi).hom =
      (restrictObj_comp x (stageHom hi) (c.π.app i')).hom ≫
        (restrictObj_eq x
          (Cone.w c (homOfLE (OrderDual.toDual_le_toDual.mpr hi)))).hom :=
  sorry

/-- The transition map of fibre Hom-types along a later bonding map of the inverse
system. -/
def restrictHomAlongStage {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i : I} (x y : (p f).Fiber (D.obj i)) {j j' : Set.Ici i} (h : j ⟶ j')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictObj x (stageHom j'.2) ⟶ restrictObj y (stageHom j'.2) :=
  (restrictObj_stage f x j.2 (leOfHom h) j'.2).inv ≫
    restrictHom φ (stageHom (leOfHom h)) ≫
    (restrictObj_stage f y j.2 (leOfHom h) j'.2).hom

/-- `restrictHomAlongStage` transports a fibre morphism by restriction along the
bonding map and the iterated-restriction comparison. -/
theorem restrictHomAlongStage_apply {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i : I} (x y : (p f).Fiber (D.obj i))
    {j j' : Set.Ici i} (h : j ⟶ j')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomAlongStage f x y h φ =
      (restrictObj_stage f x j.2 (leOfHom h) j'.2).inv ≫
        restrictHom φ (stageHom (leOfHom h)) ≫
        (restrictObj_stage f y j.2 (leOfHom h) j'.2).hom :=
  sorry

/-- The directed diagram of fibre Hom-types of restrictions of a stage pair along
bonding maps. -/
def homFunctor {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} {i : I}
    (x y : (p f).Fiber (D.obj i)) : Set.Ici i ⥤ Type (u + 1) where
  obj j := restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)
  map h := TypeCat.ofHom.{u + 1} (restrictHomAlongStage f x y h)
  map_id := sorry
  map_comp := sorry

/-- The object map of `homFunctor` is the fibre Hom-type after restriction along
the bonding map of that stage. -/
theorem homFunctor_obj {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    {i : I} (x y : (p f).Fiber (D.obj i)) (j : Set.Ici i) :
    (homFunctor f x y).obj j =
      (restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :=
  sorry

/-- The cocone leg sending a later-stage fibre morphism to its restriction along
the cone projection. -/
def restrictHomToLimit {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i : I} (x y : (p f).Fiber (D.obj i)) (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i) :=
  (restrictObj_cone f c x j.2).inv ≫
    restrictHom φ (c.π.app j.1) ≫ (restrictObj_cone f c y j.2).hom

/-- `restrictHomToLimit` is restriction along the cone projection, transported by
`restrictObj_cone`. -/
theorem restrictHomToLimit_apply {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I}
    (x y : (p f).Fiber (D.obj i)) (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomToLimit f c x y j φ =
      (restrictObj_cone f c x j.2).inv ≫
        restrictHom φ (c.π.app j.1) ≫ (restrictObj_cone f c y j.2).hom :=
  sorry

/-- The canonical cocone from the directed Hom-diagram of a stage pair to the
fibre Hom-type over the cone point. -/
def homCocone {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S} (c : Cone D)
    {i : I} (x y : (p f).Fiber (D.obj i)) : Cocone (homFunctor f x y) where
  pt := restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i)
  ι :=
    { app := fun j ↦ TypeCat.ofHom.{u + 1} (restrictHomToLimit f c x y j)
      naturality := sorry }

/-- The vertex of `homCocone` is the fibre Hom-type of the restrictions of `x`
and `y` to the cone point. -/
theorem homCocone_pt {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i : I} (x y : (p f).Fiber (D.obj i)) :
    (homCocone f c x y).pt =
      (restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i)) :=
  sorry

/-- The components of `homCocone.ι` are `restrictHomToLimit`. -/
theorem homCocone_ι_app {I : Type u} [Preorder I] {D : OrderDual I ⥤ Over S}
    (c : Cone D) {i : I} (x y : (p f).Fiber (D.obj i)) (j : Set.Ici i) :
    (homCocone f c x y).ι.app j =
      TypeCat.ofHom.{u + 1} (restrictHomToLimit f c x y j) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
