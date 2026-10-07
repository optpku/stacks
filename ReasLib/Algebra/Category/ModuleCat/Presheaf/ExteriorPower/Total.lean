module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import ReasLib.CategoryTheory.GradedObject.Total.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total exterior powers of module presheaves

Sectionwise exterior powers form a graded functor of dependent module presheaves. This file owns
their total coproduct independently of any exterior-algebra comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace PresheafOfModules.ExteriorPower.Total

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Sectionwise exterior powers assembled as a graded functor of module presheaves. -/
@[stacks 01CF "graded exterior-power functor on module presheaves"]
noncomputable def gradedFunctor :
    PresheafOfModules.{w} (RingPresheaf O) ⥤
      GradedObject ℕ (PresheafOfModules.{w} (RingPresheaf O)) :=
  Functor.pi' fun n : ℕ ↦ ExteriorPower.functor O n

/-- The total sectionwise exterior-power functor on module presheaves. -/
@[stacks 01CF "total exterior-power functor on module presheaves"]
noncomputable def functor :
    PresheafOfModules.{w} (RingPresheaf O) ⥤
      PresheafOfModules.{w} (RingPresheaf O) :=
  gradedFunctor O ⋙ GradedObject.Total.functor

/-- The graded exterior-power object associated to a module presheaf. -/
abbrev gradedObject (F : PresheafOfModules.{w} (RingPresheaf O)) :
    GradedObject ℕ (PresheafOfModules.{w} (RingPresheaf O)) :=
  (gradedFunctor O).obj F

/-- The degree-`n` piece of `gradedObject` is the sectionwise exterior-power presheaf. -/
theorem gradedObject_apply
    (F : PresheafOfModules.{w} (RingPresheaf O)) (n : ℕ) :
    gradedObject O F n = ExteriorPower.presheaf O F n := sorry

/-- The total exterior-power object is the coproduct of the degreewise presheaves. -/
theorem functor_obj (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (functor O).obj F = ∐ fun n : ℕ ↦ ExteriorPower.presheaf O F n := sorry

/-- Total exterior powers map a presheaf morphism degreewise. -/
@[simp]
theorem functor_map
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    (functor O).map f =
      Limits.Sigma.map (fun n : ℕ ↦ ExteriorPower.hom O f n) := sorry

end PresheafOfModules.ExteriorPower.Total
