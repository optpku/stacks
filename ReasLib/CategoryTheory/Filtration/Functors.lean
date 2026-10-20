module

public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.CategoryTheory.Filtration.Preadditive
public import ReasLib.CategoryTheory.GradedObject.Instances

/-!
# Functors on Filtered Objects

This module owns the category-independent functors attached to a filtered object:
stage evaluation, quotients by a stage, and the associated-graded construction. Complex-level
facades import this file; the owner does not depend on the cochain-complex specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject

/-! ## The stage functor -/

namespace Stage

/-- The `p`-th filtration-stage functor on filtered objects. -/
@[stacks 0121 "filtration stage functor"]
def functor (p : ℤ) : FilteredObject C ⥤ C where
  obj A := A.stage p
  map f := f.stageMap p
  map_id A := Hom.stageMap_id A p
  map_comp f g := Hom.stageMap_comp f g p

/-- Evaluation of the stage functor on objects. -/
@[simp]
theorem functor_obj (A : FilteredObject C) (p : ℤ) :
    (functor p).obj A = A.filtration.stage p := sorry

/-- Evaluation of the stage functor on morphisms. -/
@[simp]
theorem functor_map {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    (functor p).map f = f.stageMap p := sorry

/-- The canonical inclusion of the `p`-th stage into the underlying object, functorially. -/
@[stacks 0121 "stage inclusion"]
def toForget (p : ℤ) :
    (functor p : FilteredObject C ⥤ C) ⟶
      (FilteredObject.forget : FilteredObject C ⥤ C) where
  app A := (A.filtration.stage p).arrow
  naturality := fun {_ _} f ↦ Hom.stageMap_arrow f p

namespace Comparison

/-- A filtered morphism commutes with the comparison from its `q`-th stage to its `p`-th stage. -/
theorem naturality {A B : FilteredObject C} (f : A ⟶ B) {p q : ℤ}
    (hpq : p ≤ q) :
    A.filtration.inclusion hpq ≫ f.stageMap p =
      f.stageMap q ≫ B.filtration.inclusion hpq := sorry

end Comparison

/-- For `p ≤ q`, the `q`-th stage functor maps naturally to the `p`-th stage functor. -/
@[stacks 0121 "stage comparison"]
def mapOfLE {p q : ℤ} (hpq : p ≤ q) :
    (functor q : FilteredObject C ⥤ C) ⟶ functor p where
  app A := A.filtration.inclusion hpq
  naturality := fun {_ _} f ↦ (Comparison.naturality f hpq).symm

namespace Comparison

/-- Successive stage comparisons compose to the direct comparison. -/
theorem comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    (mapOfLE hqr : (functor r : FilteredObject C ⥤ C) ⟶ functor q) ≫
      mapOfLE hpq = mapOfLE (hpq.trans hqr) := sorry

/-- The comparison `F^q A ⟶ F^p A` followed by inclusion into `A` is the inclusion `F^q A ⟶ A`. -/
theorem comp_toForget {p q : ℤ} (hpq : p ≤ q) :
    (mapOfLE hpq : (functor q : FilteredObject C ⥤ C) ⟶ functor p) ≫
      toForget p = toForget q := sorry

end Comparison

end Stage

/-! ## Zero-morphism preservation -/

section ZeroMorphisms

variable [HasZeroMorphisms C]

/-- The induced map on a filtration stage preserves zero morphisms. -/
theorem Hom.stageMap_zero (X Y : FilteredObject C) (p : ℤ) :
    (0 : X ⟶ Y).stageMap p = 0 := sorry

instance (p : ℤ) : ((Stage.functor p : FilteredObject C ⥤ C)).PreservesZeroMorphisms where
  map_zero X Y := Hom.stageMap_zero X Y p

instance : ((FilteredObject.forget : FilteredObject C ⥤ C)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Evaluation at a fixed degree preserves zero morphisms on graded objects. -/
instance GradedObject.eval_preservesZeroMorphisms (p : ℤ) :
    (GradedObject.eval p : GradedObject ℤ C ⥤ C).PreservesZeroMorphisms where
  map_zero _ _ := rfl

end ZeroMorphisms

section StagePreadditive

variable [Preadditive C]

/-- The induced map on filtration stages preserves addition. -/
private theorem Hom.stageMap_add {X Y : FilteredObject C} (f g : X ⟶ Y) (p : ℤ) :
    (f + g).stageMap p = f.stageMap p + g.stageMap p := by
  apply (cancel_mono (Y.filtration.stage p).arrow).1
  simp [Preadditive.add_comp, Preadditive.comp_add]

/-- The filtration-stage functor is additive in a preadditive ambient category. -/
@[stacks 0121 "filtration stage functor is additive"]
instance (p : ℤ) : (Stage.functor p : FilteredObject C ⥤ C).Additive where
  map_add {X Y : FilteredObject C} {f g : X ⟶ Y} := Hom.stageMap_add f g p

end StagePreadditive

/-! ## The quotient functor -/

section Quotients

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The quotient object `A / F^p A`. -/
abbrev quotient (A : FilteredObject C) (p : ℤ) : C :=
  cokernel (A.filtration.stage p).arrow

namespace Hom

variable {X Y Z : FilteredObject C}

/-- The map induced by a filtered morphism on the quotients `A / F^p A ⟶ B / F^p B`. -/
abbrev quotientMap (f : X ⟶ Y) (p : ℤ) : X.quotient p ⟶ Y.quotient p :=
  cokernel.map (X.filtration.stage p).arrow (Y.filtration.stage p).arrow
    (f.stageMap p) f.hom (Hom.stageMap_arrow f p).symm

/-- The map on quotients commutes with the cokernel projections. -/
theorem quotientMap_comm (f : X ⟶ Y) (p : ℤ) :
    cokernel.π (X.filtration.stage p).arrow ≫ f.quotientMap p =
      f.hom ≫ cokernel.π (Y.filtration.stage p).arrow := by
  simp [quotientMap]

/-- The induced map on quotients preserves identities. -/
theorem quotientMap_id (X : FilteredObject C) (p : ℤ) :
    (𝟙 X : X ⟶ X).quotientMap p = 𝟙 (X.quotient p) := sorry

/-- The induced map on quotients preserves composition. -/
theorem quotientMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ) :
    (f ≫ g).quotientMap p = f.quotientMap p ≫ g.quotientMap p := sorry

/-- The induced map on quotients preserves zero morphisms. -/
theorem quotientMap_zero (X Y : FilteredObject C) (p : ℤ) :
    (0 : X ⟶ Y).quotientMap p = 0 := sorry

end Hom

/-- The quotient-by-`F^p` functor on filtered objects. -/
@[stacks 0121 "quotient by a filtration stage"]
def quotientFunctor (p : ℤ) : FilteredObject C ⥤ C where
  obj A := A.quotient p
  map f := f.quotientMap p
  map_id A := Hom.quotientMap_id A p
  map_comp f g := Hom.quotientMap_comp f g p

/-- Evaluation of the quotient functor on objects. -/
@[simp]
theorem quotientFunctor_obj (A : FilteredObject C) (p : ℤ) :
    (quotientFunctor p).obj A = A.quotient p := sorry

/-- Evaluation of the quotient functor on morphisms. -/
@[simp]
theorem quotientFunctor_map {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    (quotientFunctor p).map f = f.quotientMap p := sorry

instance (p : ℤ) : ((quotientFunctor p : FilteredObject C ⥤ C)).PreservesZeroMorphisms where
  map_zero X Y := Hom.quotientMap_zero X Y p

end Quotients

/-! ## The associated graded functor -/

section Graded

variable [HasZeroMorphisms C] [HasCokernels C]

namespace Hom

variable {X Y Z : FilteredObject C}

/-- The morphism induced by a filtered morphism on the `p`-th graded pieces. -/
noncomputable def gradedPieceMap (f : X ⟶ Y) (p : ℤ) : X.gradedPiece p ⟶ Y.gradedPiece p :=
  cokernel.map (X.filtration.succInclusion p) (Y.filtration.succInclusion p)
    (f.stageMap (p + 1)) (f.stageMap p)
    (succInclusion_naturality f p)

/-- The morphism induced on associated graded objects by a filtered morphism. -/
noncomputable def associatedGradedMap (f : X ⟶ Y) : X.associatedGraded ⟶ Y.associatedGraded :=
  fun p ↦ f.gradedPieceMap p

/-- The induced map on graded pieces preserves identities. -/
theorem gradedPieceMap_id (X : FilteredObject C) (p : ℤ) :
    (𝟙 X : X ⟶ X).gradedPieceMap p = 𝟙 (X.gradedPiece p) := sorry

/-- The induced map on graded pieces preserves composition. -/
theorem gradedPieceMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ) :
    (f ≫ g).gradedPieceMap p = f.gradedPieceMap p ≫ g.gradedPieceMap p := sorry

/-- The induced map on graded pieces preserves zero morphisms. -/
theorem gradedPieceMap_zero (X Y : FilteredObject C) (p : ℤ) :
    (0 : X ⟶ Y).gradedPieceMap p = 0 := sorry

/-- A zero composite of filtered morphisms induces a zero composite on every graded piece. -/
theorem gradedPieceMap_comp_zero (f : X ⟶ Y) (g : Y ⟶ Z) (hcomp : f ≫ g = 0) (p : ℤ) :
    f.gradedPieceMap p ≫ g.gradedPieceMap p = 0 := sorry

/-- The induced map on associated graded objects preserves identities. -/
theorem associatedGradedMap_id (X : FilteredObject C) :
    (𝟙 X : X ⟶ X).associatedGradedMap = 𝟙 X.associatedGraded := sorry

/-- The induced map on associated graded objects preserves composition. -/
theorem associatedGradedMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).associatedGradedMap = f.associatedGradedMap ≫ g.associatedGradedMap := sorry

/-- Evaluating the associated-graded map of a composite gives the composite of the evaluated
graded-piece maps. -/
theorem associatedGradedMap_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ) :
    ((f ≫ g).associatedGradedMap) p = f.associatedGradedMap p ≫ g.associatedGradedMap p := sorry

/-- The induced map on associated graded objects preserves zero morphisms. -/
theorem associatedGradedMap_zero (X Y : FilteredObject C) :
    (0 : X ⟶ Y).associatedGradedMap = 0 := sorry

end Hom

/-- The associated graded functor on filtered objects. -/
@[stacks 0121 "associated graded functor"]
noncomputable def associatedGradedFunctor : FilteredObject C ⥤ GradedObject ℤ C where
  obj A := A.associatedGraded
  map f := f.associatedGradedMap
  map_id A := Hom.associatedGradedMap_id A
  map_comp f g := Hom.associatedGradedMap_comp f g

/-- Evaluation of the associated graded functor on objects. -/
@[simp]
theorem associatedGradedFunctor_obj (A : FilteredObject C) :
    associatedGradedFunctor.obj A = A.associatedGraded := sorry

/-- Evaluation of the associated graded functor on morphisms. -/
@[simp]
theorem associatedGradedFunctor_map {A B : FilteredObject C} (f : A ⟶ B) :
    associatedGradedFunctor.map f = f.associatedGradedMap := sorry

instance :
    ((associatedGradedFunctor : FilteredObject C ⥤ GradedObject ℤ C)).PreservesZeroMorphisms where
  map_zero X Y := Hom.associatedGradedMap_zero X Y

section Preadditive

variable [Preadditive C]

/-- The induced map on graded pieces preserves addition. -/
private theorem Hom.gradedPieceMap_add {X Y : FilteredObject C} (f g : X ⟶ Y) (p : ℤ) :
    (f + g).gradedPieceMap p = f.gradedPieceMap p + g.gradedPieceMap p := by
  refine (cancel_epi (cokernel.π (X.filtration.succInclusion p))).1 ?_
  simp [Hom.gradedPieceMap, Hom.stageMap_add]

/-- The induced map on associated graded objects preserves addition. -/
private theorem Hom.associatedGradedMap_add {X Y : FilteredObject C} (f g : X ⟶ Y) :
    (f + g).associatedGradedMap = f.associatedGradedMap + g.associatedGradedMap := sorry

instance :
    (associatedGradedFunctor : FilteredObject C ⥤ GradedObject ℤ C).Additive where
  map_add {X Y f g} := Hom.associatedGradedMap_add (X := X) (Y := Y) f g

end Preadditive

end Graded

end FilteredObject

end CategoryTheory
