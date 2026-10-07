module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap97.«97_5_0_1_Restrict»

/-!
# Limit-preserving categories fibred in groupoids

A category fibred in groupoids over `(Sch/S)_fppf` is limit preserving when every directed
inverse limit of affine schemes over `S` induces an equivalence of fibre categories, encoded
operationally by descent of fibre objects up to isomorphism and by colimits of fibre Hom-types.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TypeCat
open CategoryTheory.Functor
open CategoryTheory.Functor.Fiber
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids

variable {S : Scheme.{u}}

/-- Iterated restriction along successive bonding maps of a directed inverse system agrees
with restriction along the composite bonding map. -/
def restrictObj_stage {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i i' i'' : I} (x : X.p.Fiber (D.obj i))
    (hi : i ≤ i') (hi' : i' ≤ i'') (hii : i ≤ i'') :
    restrictObj (restrictObj x (stageHom hi)) (stageHom hi') ≅
      restrictObj x (stageHom hii) :=
  restrictObj_comp x (stageHom hi) (stageHom hi') ≪≫
    restrictObj_eq x
      ((D.map_comp (homOfLE (OrderDual.toDual_le_toDual.mpr hi'))
          (homOfLE (OrderDual.toDual_le_toDual.mpr hi))).symm.trans
        (congrArg D.map (Subsingleton.elim _ _)))

/-- The forward map of `restrictObj_stage` is the composite of `restrictObj_comp` with the
identification of the composite bonding map. -/
theorem restrictObj_stage_hom {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i i' i'' : I} (x : X.p.Fiber (D.obj i))
    (hi : i ≤ i') (hi' : i' ≤ i'') (hii : i ≤ i'') :
    (restrictObj_stage x hi hi' hii).hom =
      (restrictObj_comp x (stageHom hi) (stageHom hi')).hom ≫
        (restrictObj_eq x
          ((D.map_comp (homOfLE (OrderDual.toDual_le_toDual.mpr hi'))
              (homOfLE (OrderDual.toDual_le_toDual.mpr hi))).symm.trans
            (congrArg D.map (Subsingleton.elim _ _)))).hom := sorry

/-- Restriction of a stage fibre object to the cone point agrees with restriction along the
cone projection of that stage. -/
def restrictObj_cone {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i i' : I} (c : Cone D) (x : X.p.Fiber (D.obj i))
    (hi : i ≤ i') :
    restrictObj (restrictObj x (stageHom hi)) (c.π.app i') ≅
      restrictObj x (c.π.app i) :=
  restrictObj_comp x (stageHom hi) (c.π.app i') ≪≫
    restrictObj_eq x (Cone.w c (homOfLE (OrderDual.toDual_le_toDual.mpr hi)))

/-- The forward map of `restrictObj_cone` is the composite of `restrictObj_comp` with the
cone-compatibility identification. -/
theorem restrictObj_cone_hom {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i i' : I} (c : Cone D) (x : X.p.Fiber (D.obj i))
    (hi : i ≤ i') :
    (restrictObj_cone c x hi).hom =
      (restrictObj_comp x (stageHom hi) (c.π.app i')).hom ≫
        (restrictObj_eq x
          (Cone.w c (homOfLE (OrderDual.toDual_le_toDual.mpr hi)))).hom := sorry

/-- The transition map of fibre Hom-types along a later bonding map of the inverse system. -/
def restrictHomAlongStage {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i : I} (x y : X.p.Fiber (D.obj i))
    {j j' : Set.Ici i} (f : j ⟶ j')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictObj x (stageHom j'.2) ⟶ restrictObj y (stageHom j'.2) :=
  (restrictObj_stage x j.2 (leOfHom f) j'.2).inv ≫
    restrictHom φ (stageHom (leOfHom f)) ≫
    (restrictObj_stage y j.2 (leOfHom f) j'.2).hom

/-- `restrictHomAlongStage` transports a fibre morphism by restriction along the bonding map
and the iterated-restriction comparison. -/
theorem restrictHomAlongStage_apply {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i : I} (x y : X.p.Fiber (D.obj i))
    {j j' : Set.Ici i} (f : j ⟶ j')
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomAlongStage x y f φ =
      (restrictObj_stage x j.2 (leOfHom f) j'.2).inv ≫
        restrictHom φ (stageHom (leOfHom f)) ≫
        (restrictObj_stage y j.2 (leOfHom f) j'.2).hom := sorry

/-- The directed diagram of fibre Hom-types of restrictions of a stage pair `x, y` along
bonding maps `T_{i'} ⟶ T_i`. -/
def homFunctor {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i : I} (x y : X.p.Fiber (D.obj i)) :
    Set.Ici i ⥤ Type u where
  obj j := restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)
  map f := TypeCat.ofHom (restrictHomAlongStage x y f)
  map_id := sorry
  map_comp := sorry

/-- The object map of `homFunctor` is the fibre Hom-type after restriction along the bonding
map of that stage. -/
theorem homFunctor_obj {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {i : I} (x y : X.p.Fiber (D.obj i)) (j : Set.Ici i) :
    (homFunctor x y).obj j =
      (restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) := sorry

/-- The cocone leg sending a later-stage fibre morphism to its restriction along the cone
projection. -/
def restrictHomToLimit {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I} (x y : X.p.Fiber (D.obj i))
    (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i) :=
  (restrictObj_cone c x j.2).inv ≫
    restrictHom φ (c.π.app j.1) ≫ (restrictObj_cone c y j.2).hom

/-- `restrictHomToLimit` is restriction along the cone projection, transported by
`restrictObj_cone`. -/
theorem restrictHomToLimit_apply {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I} (x y : X.p.Fiber (D.obj i))
    (j : Set.Ici i)
    (φ : restrictObj x (stageHom j.2) ⟶ restrictObj y (stageHom j.2)) :
    restrictHomToLimit c x y j φ =
      (restrictObj_cone c x j.2).inv ≫
        restrictHom φ (c.π.app j.1) ≫ (restrictObj_cone c y j.2).hom := sorry

/-- The canonical cocone from the directed Hom-diagram of a stage pair to the fibre Hom-type
over the cone point. -/
def homCocone {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I} (x y : X.p.Fiber (D.obj i)) :
    Cocone (homFunctor x y) where
  pt := restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i)
  ι :=
    { app := fun j ↦ TypeCat.ofHom (restrictHomToLimit c x y j)
      naturality := sorry }

/-- The vertex of `homCocone` is the fibre Hom-type of the restrictions of `x` and `y` to the
cone point. -/
theorem homCocone_pt {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I} (x y : X.p.Fiber (D.obj i)) :
    (homCocone c x y).pt =
      (restrictObj x (c.π.app i) ⟶ restrictObj y (c.π.app i)) := sorry

/-- The components of `homCocone.ι` are `restrictHomToLimit`. -/
theorem homCocone_ι_app {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I} (x y : X.p.Fiber (D.obj i))
    (j : Set.Ici i) :
    (homCocone c x y).ι.app j = TypeCat.ofHom (restrictHomToLimit c x y j) := sorry

/-- A category fibred in groupoids over `(Sch/S)_fppf` is limit preserving when directed
affine inverse limits induce equivalences of fibre categories. -/
class LimitPreserving (X : GroupoidsOver S) : Prop where
  /-- Every fibre object over the affine limit is isomorphic to the restriction of a fibre
  object over some affine stage. -/
  exists_stage : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
    (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
    ∀ x : X.p.Fiber c.pt, ∃ (i : I) (xi : X.p.Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x
  /-- Fibre Hom-types over the affine limit are the directed colimit of stage Hom-types. -/
  hom_isColimit : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
    (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
    ∀ (i : I) (x y : X.p.Fiber (D.obj i)),
      Nonempty (IsColimit (homCocone c x y))

namespace LimitPreserving

/-- Limit preservation means object descent from some affine stage together with the Hom-colimit
condition, both taken over directed affine inverse systems. -/
theorem spec (X : GroupoidsOver S) [LimitPreserving X]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left) :
    (∀ x : X.p.Fiber c.pt, ∃ (i : I) (xi : X.p.Fiber (D.obj i)),
        IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
      ∀ (i : I) (x y : X.p.Fiber (D.obj i)),
        Nonempty (IsColimit (homCocone c x y)) := sorry

/-- Being limit preserving is equivalent to object descent and Hom-colimits on every directed
affine inverse system over `S`. -/
theorem iff (X : GroupoidsOver S) :
    LimitPreserving X ↔
      (∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
        (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
        ∀ x : X.p.Fiber c.pt, ∃ (i : I) (xi : X.p.Fiber (D.obj i)),
          IsIsomorphic (restrictObj xi (c.π.app i)) x) ∧
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
        (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
        ∀ (i : I) (x y : X.p.Fiber (D.obj i)),
          Nonempty (IsColimit (homCocone c x y)) := sorry

/-- A limit-preserving category fibred in groupoids has object descent along directed affine
inverse limits. -/
theorem exists_stage_apply {X : GroupoidsOver S} [LimitPreserving X]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (x : X.p.Fiber c.pt) :
    ∃ (i : I) (xi : X.p.Fiber (D.obj i)),
      IsIsomorphic (restrictObj xi (c.π.app i)) x := sorry

/-- A limit-preserving category fibred in groupoids has Hom-colimits along directed affine
inverse limits. -/
theorem hom_isColimit_apply {X : GroupoidsOver S} [LimitPreserving X]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (i : I) (x y : X.p.Fiber (D.obj i)) :
    Nonempty (IsColimit (homCocone c x y)) := sorry

/-- The identity slice `Over.mk (𝟙 S)` is limit preserving. -/
instance sliceId : LimitPreserving (GroupoidsOver.slice (Over.mk (𝟙 S))) := sorry

/-- The canonical slice of a scheme locally of finite presentation over `S` is limit
preserving. -/
instance slice {U : Over S} [LocallyOfFinitePresentation U.hom] :
    LimitPreserving (GroupoidsOver.slice U) := sorry

/-- Limit preservation of a category fibred in groupoids implies that its structure morphism
to `(Sch/S)_fppf` is limit preserving on objects. -/
instance toLimitPreservingOnObjects {X : GroupoidsOver S} [LimitPreserving X] :
    Hom.LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X) := sorry

end LimitPreserving

end AlgebraicGeometry.Groupoids
