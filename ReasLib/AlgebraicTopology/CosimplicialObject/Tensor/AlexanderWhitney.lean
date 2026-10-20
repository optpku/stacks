/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ComplexShapeSigns.Nat
public import ReasLib.AlgebraicTopology.CosimplicialObject.Monoidal
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.AlternatingCofaceMapComplex
public import ReasLib.AlgebraicTopology.SimplexCategory.FrontBack
public import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Tensor comparison for cosimplicial objects

The front/back formula is the coefficient-independent part of the Cech cup comparison.  The
component is concrete; only its compatibility with the alternating coface differentials is a
separate proposition.  This keeps the tensor source honest and leaves coefficient-specific
bilinear constructions to their own leaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape HomologicalComplex
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.alternatingCofaceMapComplex

variable {A : Type u} [Category.{v} A] [Preadditive A] [MonoidalCategory A]
  [MonoidalPreadditive A] [HasZeroObject A] [HasCoproducts A]

namespace TensorComparison

/-- The front/back homogeneous component of the cosimplicial tensor comparison. -/
@[stacks 07MB "cosimplicial front-back tensor component"]
noncomputable def component (X Y : CosimplicialObject A) (n : ℕ) :
    (HomologicalComplex.tensorObj
      ((alternatingCofaceMapComplex A).obj X)
      ((alternatingCofaceMapComplex A).obj Y)).X n ⟶
      ((alternatingCofaceMapComplex A).obj (X ⊗ Y)).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := (alternatingCofaceMapComplex A).obj X)
    (K₂ := (alternatingCofaceMapComplex A).obj Y)
    (F := MonoidalCategory.curriedTensor A) (c := ComplexShape.up ℕ)
    (fun p q h ↦
      (X.map (SimplexCategory.frontOfAddEq p q n h)) ⊗ₘ
        (Y.map (SimplexCategory.backOfAddEq p q n h)))

/-- The front/back components commute with the alternating coface differentials. -/
@[stacks 07MB "cosimplicial front-back tensor chain condition"]
theorem component_comm (X Y : CosimplicialObject A) (i j : ℕ)
    (h : (ComplexShape.up ℕ).Rel i j) :
    component X Y i ≫ ((alternatingCofaceMapComplex A).obj (X ⊗ Y)).d i j =
      (HomologicalComplex.tensorObj
        ((alternatingCofaceMapComplex A).obj X)
        ((alternatingCofaceMapComplex A).obj Y)).d i j ≫ component X Y j := sorry

end TensorComparison

/-- 20.25.3.2 (07MB): the concrete cosimplicial front/back tensor comparison. -/
@[stacks 07MB "cosimplicial front-back tensor comparison"]
noncomputable def tensorComparison (X Y : CosimplicialObject A) :
    HomologicalComplex.tensorObj
        ((alternatingCofaceMapComplex A).obj X)
        ((alternatingCofaceMapComplex A).obj Y) ⟶
      (alternatingCofaceMapComplex A).obj (X ⊗ Y) where
  f := TensorComparison.component X Y
  comm' := fun i j h ↦ TensorComparison.component_comm X Y i j h

/-- The degreewise projection of the cosimplicial tensor comparison. -/
@[simp, stacks 07MB "cosimplicial tensor comparison degree component"]
theorem tensorComparison_f (X Y : CosimplicialObject A) (n : ℕ) :
    (tensorComparison X Y).f n = TensorComparison.component X Y n := sorry

/-- The cosimplicial tensor comparison is natural in both variables. -/
@[stacks 07MB "cosimplicial front-back tensor naturality"]
theorem tensorComparison_naturality {X X' Y Y' : CosimplicialObject A}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (HomologicalComplex.tensorHom
      ((alternatingCofaceMapComplex A).map f)
      ((alternatingCofaceMapComplex A).map g)) ≫
        tensorComparison X' Y' =
      tensorComparison X Y ≫
        (alternatingCofaceMapComplex A).map (f ⊗ₘ g) := sorry

end AlgebraicTopology.alternatingCofaceMapComplex

end
