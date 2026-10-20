module

public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap99.Lemma_99_16_4

/-!
# Hom-diagrams for the stack of complexes on a proper morphism

Lemma 99.16.4 supplies `instIsFiberedInGroupoids` and `toGroupoids` for
`p : Obj f ⥤ Over S`. Hom-types of `Obj f` live in `Type (u + 1)`, so the
bundled projection cannot inhabit `GroupoidsOver S` (which pins Hom-universe
`u`). The Artin Hom-colimit diagram is therefore built at `Type (u + 1)`,
matching `CohStack.homFunctor`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.AlgebraicSpace.Complexes
open AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
open TypeCat

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}
variable (f : X ⟶ B)
variable [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
  (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
variable [∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
  ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
  let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
  DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
variable [Proper f] [Flat f] [FinitePresentation f]

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

end AlgebraicGeometry.AlgebraicSpace.Complexes
