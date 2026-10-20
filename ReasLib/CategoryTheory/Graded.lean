/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded linear categories

This leaf owns categories whose hom modules are graded by an additive monoid. Differential graded
applications specialize the index to `ℤ`. It extends mathlib's `CategoryTheory.Linear` rather
than introducing a parallel notion of linearity.
-/

@[expose] public section

namespace CategoryTheory

universe x w v u

/-- A category enriched in `R`-modules whose hom modules have a specified direct-sum
decomposition by an additive monoid `ι`, with identities in degree zero and composition
carrying degrees `i` and `j` to degree `i + j`. -/
@[stacks 09L2]
class GradedCategory (R : Type w) [Semiring R] (C : Type u) [Category.{v} C]
    [Preadditive C] (ι : Type x) [DecidableEq ι] [AddMonoid ι] extends Linear R C where
  /-- The degree-`i` summand of the hom module from `X` to `Y`. -/
  homDegree (X Y : C) (i : ι) : Submodule R (X ⟶ Y)
  /-- The specified direct-sum decomposition of each hom module. -/
  homDecomposition (X Y : C) : DirectSum.Decomposition (homDegree X Y)
  /-- Identities have degree zero. -/
  id_mem_homDegree_zero (X : C) : 𝟙 X ∈ homDegree X X 0
  /-- Composition adds degrees. -/
  comp_mem {X Y Z : C} {i j : ι} {f : X ⟶ Y} {g : Y ⟶ Z}
      (hf : f ∈ homDegree X Y i) (hg : g ∈ homDegree Y Z j) :
      f ≫ g ∈ homDegree X Z (i + j)

namespace GradedCategory

section

variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {R : Type w} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C]

/-- The degree pieces of a graded category carry their specified direct-sum decomposition. -/
instance instHomDecomposition [h : GradedCategory R C ι] (X Y : C) :
    DirectSum.Decomposition (fun i ↦ h.homDegree X Y i) :=
  h.homDecomposition X Y

/-- The composite of two degree-zero morphisms again has degree zero. -/
theorem comp_mem_homDegree_zero [GradedCategory R C ι]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f ∈ GradedCategory.homDegree (R := R) (ι := ι) X Y 0)
    (hg : g ∈ GradedCategory.homDegree (R := R) (ι := ι) Y Z 0) :
    f ≫ g ∈ GradedCategory.homDegree (R := R) (ι := ι) X Z 0 := sorry

end

end GradedCategory

end CategoryTheory
