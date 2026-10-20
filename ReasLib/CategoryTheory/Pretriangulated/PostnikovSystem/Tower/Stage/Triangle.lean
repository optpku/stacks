module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Stage.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Triangle
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Triangle

/-!
# Stage-Triangle Functors of Sequential Postnikov Towers

This file exposes every distinguished stage triangle of a sequential Postnikov
tower as a functor, together with its computation and projection API.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower.Stage

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

variable (D) in
/-- Evaluation of a sequential Postnikov tower at its `n`th distinguished stage triangle. -/
@[stacks 0D8Z "stage-triangle functor of sequential Postnikov towers"]
def triangle (n : ℕ) : Tower D ⥤ Triangle D :=
  Triangle.functorMk (toX D (n + 1)) (toNext D n) (connecting D n)

/-- Stage-triangle evaluation returns the object-level stage triangle of the tower. -/
@[simp, stacks 0D8Z]
theorem triangle_obj (n : ℕ) (T : Tower D) :
    (triangle D n).obj T = T.triangle n := sorry

/-- Stage-triangle evaluation maps a tower morphism by its canonical triangle morphism. -/
@[simp, stacks 0D8Z]
theorem triangle_map (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    (triangle D n).map f = Hom.triangleMorphism f n := sorry

/-- The first component of a mapped stage triangle is the next auxiliary-object map. -/
@[simp, stacks 0D8Z]
theorem triangle_map_hom₁ (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    ((triangle D n).map f).hom₁ = f.yMap (n + 1) := sorry

/-- The second component of a mapped stage triangle is the next row-object map. -/
@[simp, stacks 0D8Z]
theorem triangle_map_hom₂ (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    ((triangle D n).map f).hom₂ = f.xMap (n + 1) := sorry

/-- The third component of a mapped stage triangle is the current auxiliary-object map. -/
@[simp, stacks 0D8Z]
theorem triangle_map_hom₃ (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    ((triangle D n).map f).hom₃ = f.yMap n := sorry

variable (D) in
/-- The first projection of the stage-triangle functor is next auxiliary-object evaluation. -/
@[stacks 0D8Z]
theorem triangle_comp_π₁ (n : ℕ) :
    triangle D n ⋙ Triangle.π₁ = aux D (n + 1) := sorry

variable (D) in
/-- The second projection of the stage-triangle functor is next row-object evaluation. -/
@[stacks 0D8Z]
theorem triangle_comp_π₂ (n : ℕ) :
    triangle D n ⋙ Triangle.π₂ = row D (n + 1) := sorry

variable (D) in
/-- The third projection of the stage-triangle functor is current auxiliary-object evaluation. -/
@[stacks 0D8Z]
theorem triangle_comp_π₃ (n : ℕ) :
    triangle D n ⋙ Triangle.π₃ = aux D n := sorry

variable (D) in
/-- The first structural map of the stage-triangle functor is the auxiliary-to-row comparison. -/
@[stacks 0D8Z]
theorem triangle_toX (n : ℕ) :
    Functor.whiskerLeft (triangle D n) Triangle.π₁Toπ₂ = toX D (n + 1) := sorry

variable (D) in
/-- The second structural map of the stage-triangle functor is `toNext`. -/
@[stacks 0D8Z]
theorem triangle_toNext (n : ℕ) :
    Functor.whiskerLeft (triangle D n) Triangle.π₂Toπ₃ = toNext D n := sorry

variable (D) in
/-- The third structural map of the stage-triangle functor is `connecting`. -/
@[stacks 0D8Z]
theorem triangle_connecting (n : ℕ) :
    Functor.whiskerLeft (triangle D n) Triangle.π₃Toπ₁ = connecting D n := sorry

/-- Every triangle selected by stage evaluation is distinguished. -/
@[stacks 0D8Z "distinguished stage triangle of a sequential Postnikov tower"]
theorem triangle_obj_distinguished (n : ℕ) (T : Tower D) :
    (triangle D n).obj T ∈ distTriang D := sorry

end CategoryTheory.PostnikovSystem.Tower.Stage
