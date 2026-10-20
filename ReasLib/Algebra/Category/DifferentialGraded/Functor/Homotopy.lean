/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor
public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy.Preadditive

/-!
# Actions of Differential Graded Functors on Closed and Homotopy Categories

This leaf turns a differential graded functor into functors on closed
degree-zero morphisms and on the associated homotopy categories.  It exposes
both quotient-level and represented-morphism computation API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w}
variable [DA : DifferentialGradedCategory R A] [DB : DifferentialGradedCategory R B]

namespace DgFunctor

/-- A DG functor carries closed degree-zero morphisms to closed degree-zero morphisms. -/
theorem mapCompHom_closed (F : DgFunctor R A B) {X Y : A} (f : CompHom X Y) :
    DB.d 0 (F.map f.val) = 0 := sorry

/-- The action of a DG functor on closed degree-zero morphisms. -/
def mapCompHom (F : DgFunctor R A B) {X Y : A} (f : CompHom X Y) :
    CompHom (F.obj X) (F.obj Y) :=
  ⟨F.map f.val, mapCompHom_closed F f⟩

/-- The underlying degree-zero morphism of `mapCompHom`. -/
@[simp] theorem mapCompHom_val (F : DgFunctor R A B) {X Y : A} (f : CompHom X Y) :
    (mapCompHom F f).val = F.map f.val := sorry

/-- A DG functor preserves addition of closed degree-zero morphisms. -/
@[simp] theorem mapCompHom_add (F : DgFunctor R A B) {X Y : A} (f g : CompHom X Y) :
    mapCompHom F (f + g) = mapCompHom F f + mapCompHom F g := sorry

/-- A DG functor preserves scalar multiplication of closed degree-zero morphisms. -/
@[simp] theorem mapCompHom_smul (F : DgFunctor R A B) (r : R) {X Y : A} (f : CompHom X Y) :
    mapCompHom F (r • f) = r • mapCompHom F f := sorry

/-- A DG functor carries identity closed degree-zero morphisms to identities. -/
@[simp] theorem mapCompHom_id (F : DgFunctor R A B) (X : A) :
    mapCompHom F (CompHom.id X) = CompHom.id (F.obj X) := sorry

/-- A DG functor carries composition of closed degree-zero morphisms to composition. -/
@[simp] theorem mapCompHom_comp (F : DgFunctor R A B) {X Y Z : A}
    (f : CompHom X Y) (g : CompHom Y Z) :
    mapCompHom F (CompHom.comp f g) = CompHom.comp (mapCompHom F f) (mapCompHom F g) := sorry

/-- Lemma 22.26.5 (1), Tag `09L8`: a DG functor induces a functor on closed degree-zero
morphisms. -/
@[stacks 09L8]
def mapComp (F : DgFunctor R A B) : Comp R A ⥤ Comp R B where
  obj X := ⟨F.obj X.obj⟩
  map f := mapCompHom F f
  map_id X := mapCompHom_id F X.obj
  map_comp f g := mapCompHom_comp F f g

/-- The induced functor on `Comp` acts on objects by the underlying DG functor. -/
@[simp] theorem mapComp_obj (F : DgFunctor R A B) (X : Comp R A) :
    (mapComp F).obj X = ⟨F.obj X⟩ := sorry

/-- The induced functor on `Comp` acts on morphisms by `mapCompHom`. -/
@[simp] theorem mapComp_map (F : DgFunctor R A B) {X Y : Comp R A} (f : X ⟶ Y) :
    (mapComp F).map f = mapCompHom F f := sorry

/-- The functor induced on closed degree-zero morphisms preserves addition. -/
@[simp] theorem mapComp_map_add (F : DgFunctor R A B) {X Y : Comp R A} (f g : X ⟶ Y) :
    (mapComp F).map (f + g) = (mapComp F).map f + (mapComp F).map g := sorry

/-- The functor induced on closed degree-zero morphisms preserves scalar multiplication. -/
@[simp] theorem mapComp_map_smul (F : DgFunctor R A B) (r : R) {X Y : Comp R A} (f : X ⟶ Y) :
    (mapComp F).map (r • f) = r • (mapComp F).map f := sorry

/-- A DG functor induces an additive functor on closed degree-zero morphisms. -/
instance mapComp_additive (F : DgFunctor R A B) : (mapComp F).Additive where
  map_add := fun {X Y} f g ↦ mapComp_map_add F (X := X) (Y := Y) f g

/-- A DG functor induces an `R`-linear functor on closed degree-zero morphisms. -/
instance mapComp_linear (F : DgFunctor R A B) : Functor.Linear R (mapComp F) where
  map_smul := fun {X Y} f r ↦ mapComp_map_smul F r (X := X) (Y := Y) f

/-- A DG functor preserves homotopy of closed degree-zero morphisms. -/
theorem map_homotopy {F : DgFunctor R A B} {X Y : A} {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) :
    Homotopic (F.obj X) (F.obj Y) (mapCompHom F f) (mapCompHom F g) := sorry

/-- The action of a DG functor on an individual homotopy-class hom-space. -/
def mapHomotopyClass (F : DgFunctor R A B) {X Y : A} :
    HomotopyClass X Y → HomotopyClass (F.obj X) (F.obj Y) :=
  _root_.Quotient.map (fun g ↦ mapCompHom F g) (fun _ _ hfg ↦ map_homotopy hfg)

/-- Applying `mapHomotopyClass` to a represented class maps its representative. -/
@[simp] theorem mapHomotopyClass_toHomotopyClass (F : DgFunctor R A B) {X Y : A}
    (f : CompHom X Y) :
    mapHomotopyClass F f.toHomotopyClass = (mapCompHom F f).toHomotopyClass := sorry

/-- The quotient-level action of a DG functor preserves addition. -/
@[simp] theorem mapHomotopyClass_add (F : DgFunctor R A B) {X Y : A}
    (f g : HomotopyClass X Y) :
    mapHomotopyClass F (f + g) = mapHomotopyClass F f + mapHomotopyClass F g := sorry

/-- The quotient-level action of a DG functor preserves scalar multiplication. -/
@[simp] theorem mapHomotopyClass_smul (F : DgFunctor R A B) (r : R) {X Y : A}
    (f : HomotopyClass X Y) :
    mapHomotopyClass F (r • f) = r • mapHomotopyClass F f := sorry

/-- The quotient-level action of a DG functor preserves identities. -/
theorem mapHomotopyClass_id (F : DgFunctor R A B) (X : K R A) :
    mapHomotopyClass F (kId X) = kId (⟨F.obj X.obj⟩ : K R B) := sorry

/-- The quotient-level action of a DG functor preserves composition. -/
theorem mapHomotopyClass_comp (F : DgFunctor R A B) {X Y Z : K R A}
    (f : HomotopyClass X.obj Y.obj) (g : HomotopyClass Y.obj Z.obj) :
    mapHomotopyClass F (kComp f g) =
      kComp (X := ⟨F.obj X.obj⟩) (Y := ⟨F.obj Y.obj⟩) (Z := ⟨F.obj Z.obj⟩)
        (mapHomotopyClass F f) (mapHomotopyClass F g) := sorry

/-- Lemma 22.26.5 (2), Tag `09L8`: a DG functor induces a functor on homotopy categories. -/
@[stacks 09L8]
def mapK (F : DgFunctor R A B) : K R A ⥤ K R B where
  obj X := ⟨F.obj X.obj⟩
  map f := mapHomotopyClass F f
  map_id X := mapHomotopyClass_id F X
  map_comp f g := mapHomotopyClass_comp F f g

/-- The induced functor on `K` acts on objects by the underlying DG functor. -/
@[simp] theorem mapK_obj (F : DgFunctor R A B) (X : K R A) :
    (mapK F).obj X = ⟨F.obj X⟩ := sorry

/-- `mapK` sends a represented homotopy class to the class of the mapped closed morphism. -/
@[simp] theorem mapK_map_toHomotopyClass (F : DgFunctor R A B) {X Y : A}
    (f : CompHom X Y) :
    (mapK F).map f.toHomotopyClass = (mapCompHom F f).toHomotopyClass := sorry

/-- The functor induced on homotopy categories preserves addition. -/
@[simp] theorem mapK_map_add (F : DgFunctor R A B) {X Y : K R A} (f g : X ⟶ Y) :
    (mapK F).map (f + g) = (mapK F).map f + (mapK F).map g := sorry

/-- The functor induced on homotopy categories preserves scalar multiplication. -/
@[simp] theorem mapK_map_smul (F : DgFunctor R A B) (r : R) {X Y : K R A} (f : X ⟶ Y) :
    (mapK F).map (r • f) = r • (mapK F).map f := sorry

/-- A DG functor induces an additive functor on homotopy categories. -/
instance mapK_additive (F : DgFunctor R A B) : (mapK F).Additive where
  map_add := fun {X Y} f g ↦ mapK_map_add F (X := X) (Y := Y) f g

/-- A DG functor induces an `R`-linear functor on homotopy categories. -/
instance mapK_linear (F : DgFunctor R A B) : Functor.Linear R (mapK F) where
  map_smul := fun {X Y} f r ↦ mapK_map_smul F r (X := X) (Y := Y) f

/-- On a `Comp` morphism, `mapK` is represented by the mapped closed degree-zero morphism. -/
@[simp] theorem mapK_map_compHom (F : DgFunctor R A B) {X Y : Comp R A} (f : X ⟶ Y) :
    (mapK F).map f.inK = (mapCompHom F f).toHomotopyClass := sorry

/-- The image of a closed-category morphism under `mapComp` has the expected homotopy class. -/
@[simp] theorem mapComp_map_toHomotopyClass (F : DgFunctor R A B) {X Y : Comp R A}
    (f : X ⟶ Y) :
    ((mapComp F).map f).toHomotopyClass = (mapCompHom F f).toHomotopyClass := sorry

/-- The image of a closed-category morphism under `mapComp`, then `inK`, has the expected class. -/
@[simp] theorem mapComp_map_inK (F : DgFunctor R A B) {X Y : Comp R A} (f : X ⟶ Y) :
    ((mapComp F).map f).inK = (mapCompHom F f).toHomotopyClass := sorry

/-- Applying `mapK` after `inK` agrees with applying `mapComp` and then passing to `K`. -/
@[simp] theorem mapK_map_inK (F : DgFunctor R A B) {X Y : Comp R A} (f : X ⟶ Y) :
    (mapK F).map f.inK = ((mapComp F).map f).inK := sorry

end DgFunctor

end DifferentialGradedCategory
