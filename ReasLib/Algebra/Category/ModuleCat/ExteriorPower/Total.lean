module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import ReasLib.CategoryTheory.GradedObject.Total.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total exterior powers of modules

Exterior powers form a naturally graded functor. Their total object is the coproduct of all
homogeneous degrees. This owner is independent of the comparison with the exterior algebra.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace ModuleCat.exteriorPower

variable {R : Type u} [CommRing R]

/-- Exterior powers assembled as a naturally graded functor. -/
@[stacks 01CF "graded exterior-power functor on modules"]
noncomputable def gradedFunctor :
    ModuleCat.{v} R ⥤ GradedObject ℕ (ModuleCat.{max u v} R) :=
  Functor.pi' fun n : ℕ ↦ ModuleCat.exteriorPower.functor R n

/-- The coproduct of all exterior powers, functorially in the module. -/
@[stacks 01CF "total exterior-power functor on modules"]
noncomputable def totalFunctor :
    ModuleCat.{v} R ⥤ ModuleCat.{max u v} R :=
  gradedFunctor (R := R) ⋙ GradedObject.Total.functor

/-- The degree-`n` component of the graded exterior-power functor acts by `exteriorPower.map`. -/
@[simp]
theorem gradedFunctor_map_apply {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (n : ℕ) :
    (gradedFunctor (R := R)).map f n = map f n := sorry

/-- Total exterior powers act by the coproduct of the degreewise exterior-power maps. -/
@[simp]
theorem totalFunctor_map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    (totalFunctor (R := R)).map f =
      Limits.Sigma.map (fun n : ℕ ↦ map f n) := sorry

end ModuleCat.exteriorPower
