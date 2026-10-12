/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import stacks_project.Chap46.Definition_46_3_1_ModuleValuedFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/-- Module-valued functors form a category whose morphisms have linear components over
every `A`-algebra. -/
instance instCategory : Category (ModuleValuedFunctor.{u, v} A) where
  Hom := Hom
  id F :=
    { app := fun _ ↦ 𝟙 _
      naturality := sorry }
  comp f g :=
    { app := fun B ↦ f.app B ≫ g.app B
      naturality := sorry }
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The category of module-valued functors has componentwise zero morphisms. -/
instance instHasZeroMorphisms : HasZeroMorphisms (ModuleValuedFunctor.{u, v} A) where
  zero F G :=
    { zero :=
        { app := fun _ ↦ 0
          naturality := sorry } }
  comp_zero := sorry
  zero_comp := sorry

/-- The category of module-valued functors has kernels. -/
instance instHasKernels : HasKernels (ModuleValuedFunctor.{u, v} A) := sorry

end ModuleValuedFunctor
