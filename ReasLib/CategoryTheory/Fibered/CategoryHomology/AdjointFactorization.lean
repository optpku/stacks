/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Presheaf
public import ReasLib.CategoryTheory.Fibered.CategoryHomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber homology for an adjoint factorization

For a morphism `g : X ⟶ Y` of fibered categories, the target leg of its adjoint factorization
organizes the comparison-index categories over `Y.total`. This file applies the bar fiber-homology
API to those fibers, functorially in a coefficient presheaf on `X.total`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.FiberedCategoryOver.AdjointFactorization

noncomputable section

universe u v w z

namespace CategoryTheory.FiberedCategoryOver.FiberHomology.AdjointFactorization

variable {B : Type u} [Category.{v} B]
variable {X Y : FiberedCategoryOver.{u, v, w, w} B}
variable (g : X ⟶ Y)

/-- Bar homology of the comparison-index category over one target object. -/
@[stacks 08PK "comparison-index category homology"]
noncomputable abbrev homology
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{max w z}) (y : Y.total) (n : ℕ) :
    AddCommGrpCat.{max w z} :=
  Bar.homology
    (FiberedCategoryOver.AdjointFactorization.overTarget g)
    (FiberedCategoryOver.AdjointFactorization.sourcePullback g F) y n

/-- Comparison-index bar homology as a functor of the coefficient presheaf. -/
@[stacks 08PK "comparison-index homology presheaf functor"]
noncomputable abbrev presheafFunctor (n : ℕ) :
    (X.totalᵒᵖ ⥤ AddCommGrpCat.{max w z}) ⥤
      (Y.totalᵒᵖ ⥤ AddCommGrpCat.{max w z}) :=
  sourcePullbackFunctor g ⋙
    Bar.presheafFunctor
      (FiberedCategoryOver.AdjointFactorization.overTarget g) n

/-- Comparison-index bar homology is additive in the coefficient presheaf. -/
@[stacks 08PK "additivity of comparison-index homology presheaves"]
instance presheafFunctor.additive (n : ℕ) : (presheafFunctor g n).Additive := sorry

/-- The presheaf of comparison-index bar homology on the target total category. -/
@[stacks 08PK "comparison-index homology presheaf"]
noncomputable abbrev presheaf
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{max w z}) (n : ℕ) :
    Y.totalᵒᵖ ⥤ AddCommGrpCat.{max w z} :=
  (presheafFunctor g n).obj F

/-- Evaluation of the comparison-index homology presheaf functor. -/
@[simp, stacks 08PK "comparison-index homology presheaf functor object formula"]
theorem presheafFunctor_obj
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{max w z}) (n : ℕ) :
    (presheafFunctor g n).obj F = presheaf g F n := sorry

variable (J : GrothendieckTopology Y.total)
variable [HasWeakSheafify J AddCommGrpCat.{max w z}]

/-- Comparison-index homology followed by sheafification, functorially in coefficients. -/
@[stacks 08PK "comparison-index homology sheaf functor"]
noncomputable abbrev sheafFunctor (n : ℕ) :
    (X.totalᵒᵖ ⥤ AddCommGrpCat.{max w z}) ⥤
      Sheaf J AddCommGrpCat.{max w z} :=
  sourcePullbackFunctor g ⋙
    Bar.sheafFunctor J
      (FiberedCategoryOver.AdjointFactorization.overTarget g) n

/-- Sheafified comparison-index homology is additive in the coefficient presheaf. -/
@[stacks 08PK "additivity of comparison-index homology sheaves"]
instance sheafFunctor.additive (n : ℕ) : (sheafFunctor g J n).Additive := sorry

/-- The sheafification of the comparison-index homology presheaf. -/
@[stacks 08PK "comparison-index homology sheaf"]
noncomputable abbrev sheaf
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{max w z}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{max w z} :=
  (sheafFunctor g J n).obj F

/-- Evaluation of the comparison-index homology sheaf functor. -/
@[simp, stacks 08PK "comparison-index homology sheaf functor object formula"]
theorem sheafFunctor_obj
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{max w z}) (n : ℕ) :
    (sheafFunctor g J n).obj F = sheaf g J F n := sorry

variable (K : GrothendieckTopology X.total)

/-- Comparison-index homology on sheaves of coefficients on the source total category. -/
@[stacks 08PK "comparison-index homology functor on sheaves"]
noncomputable abbrev sheafOfSheafFunctor (n : ℕ) :
    Sheaf K AddCommGrpCat.{max w z} ⥤
      Sheaf J AddCommGrpCat.{max w z} :=
  sheafToPresheaf K AddCommGrpCat.{max w z} ⋙ sheafFunctor g J n

/-- Comparison-index homology is additive in source sheaves. -/
@[stacks 08PK "additivity of comparison-index homology on sheaves"]
instance sheafOfSheafFunctor.additive (n : ℕ) :
    (sheafOfSheafFunctor g J K n).Additive := sorry

/-- The comparison-index homology sheaf attached to a source sheaf. -/
@[stacks 08PK "comparison-index homology sheaf of a sheaf"]
noncomputable abbrev sheafOfSheaf
    (F : Sheaf K AddCommGrpCat.{max w z}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{max w z} :=
  (sheafOfSheafFunctor g J K n).obj F

/-- Evaluation of the comparison-index homology functor on a source sheaf. -/
@[simp, stacks 08PK "comparison-index homology functor object formula"]
theorem sheafOfSheafFunctor_obj
    (F : Sheaf K AddCommGrpCat.{max w z}) (n : ℕ) :
    (sheafOfSheafFunctor g J K n).obj F = sheafOfSheaf g J K F n := sorry

end CategoryTheory.FiberedCategoryOver.FiberHomology.AdjointFactorization
