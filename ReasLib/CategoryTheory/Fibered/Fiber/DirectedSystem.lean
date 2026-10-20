module

public import ReasLib.CategoryTheory.Fibered.Fiber.Restriction
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Fibre Hom-diagrams over inverse systems

Restriction in a fibred category gives canonical stage comparisons, diagrams of
fibre Hom-types on final segments, and cocones over inverse-system cone points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uB uE vB vE uI

namespace CategoryTheory.Functor.Fiber.DirectedSystem

variable {B : Type uB} {E : Type uE} [Category.{vB} B] [Category.{vE} E]

/-- The bonding map from a later stage to an earlier stage of an inverse system. -/
def stageHom {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B} {i i' : I}
    (hi : i ≤ i') : D.obj i' ⟶ D.obj i :=
  D.map (homOfLE (OrderDual.toDual_le_toDual.mpr hi))

variable (p : E ⥤ B) [p.IsFibered]

/-- Iterated restriction along successive bonding maps of a directed inverse
system agrees with restriction along the composite bonding map. -/
def restrictObj_stage {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B}
    {i i' i'' : I} (x : p.Fiber (D.obj i))
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
theorem restrictObj_stage_hom {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B}
    {i i' i'' : I} (x : p.Fiber (D.obj i))
    (hi : i ≤ i') (hi' : i' ≤ i'') (hii : i ≤ i'') :
    (restrictObj_stage p x hi hi' hii).hom =
      (restrictObj_comp x (stageHom hi) (stageHom hi')).hom ≫
        (restrictObj_eq x
          ((D.map_comp (homOfLE (OrderDual.toDual_le_toDual.mpr hi'))
              (homOfLE (OrderDual.toDual_le_toDual.mpr hi))).symm.trans
            (congrArg D.map (Subsingleton.elim _ _)))).hom :=
  rfl

/-- Restriction of a stage fibre object to the cone point agrees with restriction
along the cone projection of that stage. -/
def restrictObj_cone {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B}
    {i i' : I} (c : Cone D) (x : p.Fiber (D.obj i))
    (hi : i ≤ i') :
    restrictObj (restrictObj x (stageHom hi)) (c.π.app i') ≅
      restrictObj x (c.π.app i) :=
  restrictObj_comp x (stageHom hi) (c.π.app i') ≪≫
    restrictObj_eq x (Cone.w c (homOfLE (OrderDual.toDual_le_toDual.mpr hi)))

/-- The forward map of `restrictObj_cone` is the composite of `restrictObj_comp`
with the cone-compatibility identification. -/
theorem restrictObj_cone_hom {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B}
    {i i' : I} (c : Cone D) (x : p.Fiber (D.obj i))
    (hi : i ≤ i') :
    (restrictObj_cone p c x hi).hom =
      (restrictObj_comp x (stageHom hi) (c.π.app i')).hom ≫
        (restrictObj_eq x
          (Cone.w c (homOfLE (OrderDual.toDual_le_toDual.mpr hi)))).hom :=
  rfl

/-- The transition map of fibre Hom-types along a later bonding map of the inverse
system. -/
def restrictHomAlongStage {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B}
    {i : I} (x y : p.Fiber (D.obj i))
    {j j' : Set.Ici i} (h : j ⟶ j')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictObj x (stageHom j'.2) ⟶ restrictObj y (stageHom j'.2) :=
  (restrictObj_stage p x j.2 (leOfHom h) j'.2).inv ≫
    restrictHom φ (stageHom (leOfHom h)) ≫
    (restrictObj_stage p y j.2 (leOfHom h) j'.2).hom

/-- `restrictHomAlongStage` transports a fibre morphism by restriction along the
bonding map and the iterated-restriction comparison. -/
theorem restrictHomAlongStage_apply {I : Type uI} [Preorder I]
    {D : OrderDual I ⥤ B} {i : I}
    (x y : p.Fiber (D.obj i)) {j j' : Set.Ici i}
    (h : j ⟶ j')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomAlongStage p x y h φ =
      (restrictObj_stage p x j.2 (leOfHom h) j'.2).inv ≫
        restrictHom φ (stageHom (leOfHom h)) ≫
        (restrictObj_stage p y j.2 (leOfHom h) j'.2).hom :=
  rfl

/-- Transition along an identity stage map fixes every fibre morphism. -/
theorem restrictHomAlongStage_id {I : Type uI} [Preorder I]
    {D : OrderDual I ⥤ B} {i : I}
    (x y : p.Fiber (D.obj i)) (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomAlongStage p x y (𝟙 j) φ = φ :=
  sorry

/-- Transition along a composite stage map is the composite of the transitions. -/
theorem restrictHomAlongStage_comp {I : Type uI} [Preorder I]
    {D : OrderDual I ⥤ B} {i : I}
    (x y : p.Fiber (D.obj i))
    {j j' j'' : Set.Ici i} (h : j ⟶ j') (h' : j' ⟶ j'')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomAlongStage p x y (h ≫ h') φ =
      restrictHomAlongStage p x y h' (restrictHomAlongStage p x y h φ) :=
  sorry

/-- The directed diagram of fibre Hom-types of restrictions of a stage pair along
bonding maps. -/
def homFunctor {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B} {i : I}
    (x y : p.Fiber (D.obj i)) :
    Set.Ici i ⥤ Type vE where
  obj j := restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)
  map h := TypeCat.ofHom.{vE} (restrictHomAlongStage p x y h)
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact restrictHomAlongStage_id p x y j φ
  map_comp h h' := by
    apply ConcreteCategory.hom_ext
    intro φ
    exact restrictHomAlongStage_comp p x y h h' φ

/-- The object map of `homFunctor` is the fibre Hom-type after restriction along
the bonding map of that stage. -/
theorem homFunctor_obj {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B}
    {i : I} (x y : p.Fiber (D.obj i)) (j : Set.Ici i) :
    (homFunctor p x y).obj j =
      (restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :=
  rfl

/-- The cocone leg sending a later-stage fibre morphism to its restriction along
the cone projection. -/
def restrictHomToLimit {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B}
    (c : Cone D) {i : I} (x y : p.Fiber (D.obj i))
    (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i) :=
  (restrictObj_cone p c x j.2).inv ≫
    restrictHom φ (c.π.app j.1) ≫ (restrictObj_cone p c y j.2).hom

/-- `restrictHomToLimit` is restriction along the cone projection, transported by
`restrictObj_cone`. -/
theorem restrictHomToLimit_apply {I : Type uI} [Preorder I]
    {D : OrderDual I ⥤ B} (c : Cone D) {i : I}
    (x y : p.Fiber (D.obj i)) (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomToLimit p c x y j φ =
      (restrictObj_cone p c x j.2).inv ≫
        restrictHom φ (c.π.app j.1) ≫ (restrictObj_cone p c y j.2).hom :=
  rfl

/-- Restriction to the cone point commutes with transition to a later stage. -/
theorem restrictHomToLimit_naturality {I : Type uI} [Preorder I]
    {D : OrderDual I ⥤ B} (c : Cone D) {i : I}
    (x y : p.Fiber (D.obj i))
    {j j' : Set.Ici i} (h : j ⟶ j')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomToLimit p c x y j' (restrictHomAlongStage p x y h φ) =
      restrictHomToLimit p c x y j φ :=
  sorry

/-- The canonical cocone from the directed Hom-diagram of a stage pair to the
fibre Hom-type over the cone point. -/
def homCocone {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B} (c : Cone D)
    {i : I} (x y : p.Fiber (D.obj i)) :
    Cocone (homFunctor p x y) where
  pt := restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i)
  ι :=
    { app := fun j ↦ TypeCat.ofHom.{vE} (restrictHomToLimit p c x y j)
      naturality := by
        intro j j' h
        apply ConcreteCategory.hom_ext
        intro φ
        exact restrictHomToLimit_naturality p c x y h φ }

/-- The vertex of `homCocone` is the fibre Hom-type of the restrictions of `x`
and `y` to the cone point. -/
theorem homCocone_pt {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B}
    (c : Cone D) {i : I} (x y : p.Fiber (D.obj i)) :
    (homCocone p c x y).pt =
      (restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i)) :=
  rfl

/-- The components of `homCocone.ι` are `restrictHomToLimit`. -/
theorem homCocone_ι_app {I : Type uI} [Preorder I] {D : OrderDual I ⥤ B}
    (c : Cone D) {i : I} (x y : p.Fiber (D.obj i))
    (j : Set.Ici i) :
    (homCocone p c x y).ι.app j =
      TypeCat.ofHom.{vE} (restrictHomToLimit p c x y j) :=
  rfl

end CategoryTheory.Functor.Fiber.DirectedSystem
