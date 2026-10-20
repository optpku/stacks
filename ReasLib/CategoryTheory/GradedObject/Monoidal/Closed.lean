/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed structure on graded objects

For a group-graded convolution category, the degree-`n` component of the internal Hom from `X`
to `Y` is the product `∏ i, (X i ⟶[C] Y (i + n))`.  This file constructs that object and the
tensor/internal-Hom adjunction explicitly.  It is independent of rings, sheaves, and complexes.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe w u v

namespace CategoryTheory.GradedObject.InternalHom

variable {I : Type w} [AddCommGroup I]

/-- The source degrees selected in graded currying add to the target degree. -/
theorem curryDegree (i n : I) : i + n = i + n := sorry

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
variable [HasProductsOfShape I C]
variable [∀ X Y : GradedObject I C, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject I C, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject I C, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [DecidableEq I] [HasInitial C]
variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]
variable [∀ X Y Z W : GradedObject I C, GradedObject.HasTensor₄ObjExt X Y Z W]

/-- The family whose product is the degree-`n` component of graded internal Hom. -/
noncomputable abbrev family (X Y : GradedObject I C) (n : I) : I → C :=
  fun i ↦ (ihom (X i)).obj (Y (i + n))

/-- The graded internal-Hom object, with all homogeneous source degrees retained by a product. -/
@[stacks 0FR6 "graded internal Hom object"]
noncomputable abbrev obj (X Y : GradedObject I C) : GradedObject I C :=
  fun n ↦ ∏ᶜ family X Y n

/-- Postcomposition on graded internal Hom. -/
noncomputable def map (X : GradedObject I C) {Y Y' : GradedObject I C} (f : Y ⟶ Y') :
    obj X Y ⟶ obj X Y' :=
  fun n ↦ Pi.lift fun i ↦
    Pi.π (family X Y n) i ≫ (ihom (X i)).map (f (i + n))

/-- Graded internal Hom with fixed source, functorial in the target. -/
@[stacks 0FR6 "graded internal Hom functor"]
noncomputable def functor (X : GradedObject I C) :
    GradedObject I C ⥤ GradedObject I C where
  obj := obj X
  map := map X
  map_id := sorry
  map_comp := sorry

/-- Currying a graded map degreewise into the defining products. -/
noncomputable def curry {X Y Z : GradedObject I C} (f : X ⊗ Z ⟶ Y) :
    Z ⟶ obj X Y :=
  fun n ↦ Pi.lift fun i ↦
    CategoryTheory.MonoidalClosed.curry
      (GradedObject.Monoidal.ιTensorObj X Z i n (i + n) (curryDegree i n) ≫ f (i + n))

/-- Uncurrying a graded internal-Hom map on every homogeneous tensor summand. -/
noncomputable def uncurry {X Y Z : GradedObject I C} (f : Z ⟶ obj X Y) :
    X ⊗ Z ⟶ Y :=
  fun _ ↦ GradedObject.Monoidal.tensorObjDesc fun i j h ↦
    (X i ◁ f j) ≫
      (X i ◁ Pi.π (family X Y j) i) ≫
        (ihom.ev (X i)).app (Y (i + j)) ≫ eqToHom (congrArg Y h)

/-- The degreewise tensor/internal-Hom equivalence for graded objects. -/
@[stacks 0FR6 "graded tensor-Hom equivalence"]
noncomputable def homEquiv (X Z Y : GradedObject I C) :
    (X ⊗ Z ⟶ Y) ≃ (Z ⟶ obj X Y) where
  toFun := curry
  invFun := uncurry
  left_inv := sorry
  right_inv := sorry

/-- The graded tensor/internal-Hom equivalence is natural in source and target. -/
noncomputable def coreHomEquiv (X : GradedObject I C) :
    Adjunction.CoreHomEquiv (tensorLeft X) (functor X) where
  homEquiv Z Y := homEquiv X Z Y
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

/-- Tensoring by a graded object is left adjoint to its explicitly constructed graded internal
Hom functor. -/
@[stacks 0FR6 "graded tensor-Hom adjunction"]
noncomputable def adjunction (X : GradedObject I C) : tensorLeft X ⊣ functor X :=
  Adjunction.mkOfHomEquiv (coreHomEquiv X)

/-- The closed structure on a graded object supplied by products of ambient internal Homs. -/
@[implicit_reducible]
noncomputable def closed (X : GradedObject I C) : Closed X where
  rightAdj := functor X
  adj := adjunction X

/-- The convolution category of group-graded objects is monoidal closed when the ambient
category is monoidal closed and has products indexed by the grading group. -/
@[stacks 0FR6 "closed category of graded objects", instance_reducible]
noncomputable def monoidalClosed : MonoidalClosed (GradedObject I C) where
  closed := closed



end CategoryTheory.GradedObject.InternalHom

end
