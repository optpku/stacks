module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Triangle
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Stage.Basic

/-!
# Triangle Functors of Total Postnikov-System Stages

This file promotes every finite stage to a functor into mathlib's category of
triangles and exposes its projections, structural maps, and distinguishedness.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {n : ℕ}

variable (D) in
/-- Evaluation of a total finite Postnikov system at a stage, as a functor to mathlib's
category of triangles. -/
@[stacks 0D7Z "stage-triangle functor for total finite Postnikov systems"]
def triangle (n : ℕ) (i : Fin n) : Total D n ⥤ Triangle D :=
  Triangle.functorMk (toRow D n i.castSucc) (toNext D n i) (connecting D n i)

/-- The stage-triangle functor evaluates to the triangle stored by the Postnikov system. -/
@[simp, stacks 0D7Z "stage-triangle functor on objects"]
theorem triangle_obj (i : Fin n) (P : Total D n) :
    (triangle D n i).obj P = P.system.triangle i := sorry

/-- The stage-triangle functor maps a total morphism by its canonical stage triangle
morphism. -/
@[simp, stacks 0D7Z "stage-triangle functor on morphisms"]
theorem triangle_map (i : Fin n) {P Q : Total D n} (f : P ⟶ Q) :
    (triangle D n i).map f = f.systemMap.triangleMorphism i := sorry

/-- The first component of a mapped stage triangle is the corresponding auxiliary map. -/
@[simp, stacks 0D7Z]
theorem triangle_map_hom₁ (i : Fin n) {P Q : Total D n} (f : P ⟶ Q) :
    ((triangle D n i).map f).hom₁ = f.systemMap.yMap i.castSucc := sorry

/-- The second component of a mapped stage triangle is the corresponding row-map
component. -/
@[simp, stacks 0D7Z]
theorem triangle_map_hom₂ (i : Fin n) {P Q : Total D n} (f : P ⟶ Q) :
    ((triangle D n i).map f).hom₂ = f.base.app i.castSucc := sorry

/-- The third component of a mapped stage triangle is the next auxiliary map. -/
@[simp, stacks 0D7Z]
theorem triangle_map_hom₃ (i : Fin n) {P Q : Total D n} (f : P ⟶ Q) :
    ((triangle D n i).map f).hom₃ = f.systemMap.yMap i.succ := sorry

variable (D) in
/-- The first projection of the stage-triangle functor is auxiliary evaluation at the current
stage. -/
@[stacks 0D7Z "first projection of the total Postnikov-stage triangle"]
theorem triangle_comp_π₁ (n : ℕ) (i : Fin n) :
    triangle D n i ⋙ Triangle.π₁ = aux D n i.castSucc := sorry

variable (D) in
/-- The second projection of the stage-triangle functor is row evaluation at the current
stage. -/
@[stacks 0D7Z "second projection of the total Postnikov-stage triangle"]
theorem triangle_comp_π₂ (n : ℕ) (i : Fin n) :
    triangle D n i ⋙ Triangle.π₂ = row D n i.castSucc := sorry

variable (D) in
/-- The third projection of the stage-triangle functor is auxiliary evaluation at the next
stage. -/
@[stacks 0D7Z "third projection of the total Postnikov-stage triangle"]
theorem triangle_comp_π₃ (n : ℕ) (i : Fin n) :
    triangle D n i ⋙ Triangle.π₃ = aux D n i.succ := sorry

variable (D) in
/-- The first structural natural transformation of `triangle` is `toRow`. -/
@[stacks 0D7Z "first structural map of the total Postnikov-stage triangle"]
theorem triangle_toRow (n : ℕ) (i : Fin n) :
    Functor.whiskerLeft (triangle D n i) Triangle.π₁Toπ₂ =
      toRow D n i.castSucc := sorry

variable (D) in
/-- The second structural natural transformation of `triangle` is `toNext`. -/
@[stacks 0D7Z "second structural map of the total Postnikov-stage triangle"]
theorem triangle_toNext (n : ℕ) (i : Fin n) :
    Functor.whiskerLeft (triangle D n i) Triangle.π₂Toπ₃ =
      toNext D n i := sorry

variable (D) in
/-- The third structural natural transformation of `triangle` is `connecting`. -/
@[stacks 0D7Z "third structural map of the total Postnikov-stage triangle"]
theorem triangle_connecting (n : ℕ) (i : Fin n) :
    Functor.whiskerLeft (triangle D n i) Triangle.π₃Toπ₁ =
      connecting D n i := sorry

/-- Every object selected by the stage-triangle functor is distinguished. -/
@[stacks 0D7Z "distinguished total Postnikov-stage triangle"]
theorem triangle_obj_distinguished (i : Fin n) (P : Total D n) :
    (triangle D n i).obj P ∈ distTriang D := sorry

end CategoryTheory.PostnikovSystem.Total
