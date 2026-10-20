module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Order.WithBot

/-!
# Finite decreasing filtration diagrams

A decreasing filtration is represented by a diagram on the dual integers with an
adjoined top element for the underlying object. Finite filtrations have monic stage
inclusions, a stage equal to the whole object, and a zero stage.
-/

@[expose] public section

universe v u

namespace CategoryTheory.FiniteFilteredDiagram

open Limits

/-- The index category of a decreasing integer filtration with an underlying object. -/
abbrev Index := WithTop ℤᵒᵈ

/-- The index of the filtration stage at an integer. -/
def stageIndex (degree : ℤ) : Index := (OrderDual.toDual degree : ℤᵒᵈ)

/-- The canonical arrow from an integer stage to the underlying-object index. -/
def stageToTop (degree : ℤ) : stageIndex degree ⟶ (⊤ : Index) :=
  homOfLE le_top

/-- The canonical arrow from the next filtration stage to the current stage. -/
def stageStep (degree : ℤ) : stageIndex (degree + 1) ⟶ stageIndex degree :=
  homOfLE (WithTop.coe_le_coe.mpr (Int.le_add_one (le_refl degree)))

variable {C : Type u} [Category.{v} C]

/-- A diagram is a finite filtration when its stages embed in the underlying object,
one stage is the whole object, and one stage is zero. -/
def IsFinite (diagram : Index ⥤ C) : Prop :=
  (∀ degree : ℤ, Mono (diagram.map (stageToTop degree))) ∧
    (∃ degree : ℤ, IsIso (diagram.map (stageToTop degree))) ∧
    ∃ degree : ℤ, IsZero (diagram.obj (stageIndex degree))

/-- The full subcategory of diagrams representing finite decreasing filtrations. -/
abbrev category (C : Type u) [Category.{v} C] :=
  ObjectProperty.FullSubcategory (IsFinite (C := C))

/-- The underlying object of a finite filtration diagram. -/
def underlying (diagram : category C) : C := diagram.obj.obj ⊤

/-- The object at an integer stage of a finite filtration diagram. -/
def stage (diagram : category C) (degree : ℤ) : C :=
  diagram.obj.obj (stageIndex degree)

/-- The inclusion of a filtration stage into its underlying object. -/
def inclusion (diagram : category C) (degree : ℤ) :
    stage diagram degree ⟶ underlying diagram :=
  diagram.obj.map (stageToTop degree)

/-- The transition from the next filtration stage to the current stage. -/
def transition (diagram : category C) (degree : ℤ) :
    stage diagram (degree + 1) ⟶ stage diagram degree :=
  diagram.obj.map (stageStep degree)

/-- Every stage inclusion in a finite filtration diagram is monic. -/
instance inclusion_mono (diagram : category C) (degree : ℤ) :
    Mono (inclusion diagram degree) := diagram.property.1 degree

/-- A transition followed by a stage inclusion is the next stage inclusion. -/
@[simp]
theorem transition_inclusion (diagram : category C) (degree : ℤ) :
    transition diagram degree ≫ inclusion diagram degree =
      inclusion diagram (degree + 1) := by
  change diagram.obj.map _ ≫ diagram.obj.map _ = diagram.obj.map _
  rw [← diagram.obj.map_comp]
  congr 1

/-- A morphism of finite filtration diagrams commutes with the stage inclusions. -/
theorem inclusion_naturality {diagram target : category C} (morphism : diagram ⟶ target)
    (degree : ℤ) :
    inclusion diagram degree ≫ morphism.hom.app ⊤ =
      morphism.hom.app (stageIndex degree) ≫ inclusion target degree :=
  morphism.hom.naturality (stageToTop degree)

/-- Evaluation at the underlying-object index forgets a finite filtration. -/
def underlyingFunctor (C : Type u) [Category.{v} C] : category C ⥤ C where
  obj := underlying
  map morphism := morphism.hom.app ⊤

/-- Underlying evaluation returns the underlying object of the diagram. -/
@[simp]
theorem underlyingFunctor_obj (diagram : category C) :
    (underlyingFunctor C).obj diagram = underlying diagram := rfl

/-- Underlying evaluation takes the component at the top index of a morphism. -/
@[simp]
theorem underlyingFunctor_map {diagram target : category C} (morphism : diagram ⟶ target) :
    (underlyingFunctor C).map morphism = morphism.hom.app ⊤ := rfl

/-- Underlying evaluation preserves zero morphisms. -/
instance underlyingFunctor_preservesZeroMorphisms [HasZeroMorphisms C] :
    (underlyingFunctor C).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- A morphism is a strict monomorphism when its underlying map is monic and each
stage-to-underlying naturality square is Cartesian. -/
def IsStrictMono {diagram target : category C} (morphism : diagram ⟶ target) : Prop :=
  Mono ((underlyingFunctor C).map morphism) ∧
    ∀ degree : ℤ, IsPullback (inclusion diagram degree)
      (morphism.hom.app (stageIndex degree)) ((underlyingFunctor C).map morphism)
      (inclusion target degree)

variable [Abelian C]

/-- The associated graded object in an integer degree is the cokernel of the
transition from the next filtration stage. -/
noncomputable def gradedPieceFunctor (degree : ℤ) : category C ⥤ C where
  obj diagram := cokernel (transition diagram degree)
  map {diagram target} morphism :=
    cokernel.map (transition diagram degree) (transition target degree)
      (morphism.hom.app (stageIndex (degree + 1))) (morphism.hom.app (stageIndex degree))
      (morphism.hom.naturality (stageStep degree))
  map_id diagram := by
    apply (cancel_epi (cokernel.π (transition diagram degree))).1
    simp [cokernel.map]
    exact Category.id_comp _
  map_comp first second := by
    apply (cancel_epi (cokernel.π (transition _ degree))).1
    simp [cokernel.map, Category.assoc]
    exact Category.assoc _ _ _

/-- The graded piece of a finite filtration is the cokernel of its stage transition. -/
@[simp]
theorem gradedPieceFunctor_obj (degree : ℤ) (diagram : category C) :
    (gradedPieceFunctor (C := C) degree).obj diagram =
      cokernel (transition diagram degree) := rfl

/-- A map on graded pieces is induced by the naturality square of stage transitions. -/
theorem gradedPieceFunctor_map (degree : ℤ) {diagram target : category C}
    (morphism : diagram ⟶ target) :
    (gradedPieceFunctor (C := C) degree).map morphism =
      cokernel.map (transition diagram degree) (transition target degree)
        (morphism.hom.app (stageIndex (degree + 1))) (morphism.hom.app (stageIndex degree))
        (morphism.hom.naturality (stageStep degree)) := rfl

/-- The projection to a graded piece commutes with every filtered morphism. -/
@[simp]
theorem gradedPieceFunctor_π_map (degree : ℤ) {diagram target : category C}
    (morphism : diagram ⟶ target) :
    cokernel.π (transition diagram degree) ≫
        (gradedPieceFunctor (C := C) degree).map morphism =
      morphism.hom.app (stageIndex degree) ≫ cokernel.π (transition target degree) := by
  simp [gradedPieceFunctor, cokernel.map]
  rfl

/-- Taking an associated graded piece preserves zero morphisms. -/
instance gradedPieceFunctor_preservesZeroMorphisms (degree : ℤ) :
    (gradedPieceFunctor (C := C) degree).PreservesZeroMorphisms where
  map_zero diagram target := by
    simp [gradedPieceFunctor]
    exact cokernel.map_zero _ _ _ _

/-- A finite filtration diagram is filtered injective when every graded piece is
an injective object. -/
def IsFilteredInjective (diagram : category C) : Prop :=
  ∀ degree : ℤ, Injective ((gradedPieceFunctor (C := C) degree).obj diagram)

end CategoryTheory.FiniteFilteredDiagram
