/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Category.FGModuleCat.Basic

@[expose] public section

universe uR uC vC uD vD

namespace CategoryTheory.Functor

variable (R : Type uR) [Semiring R]
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [Preadditive C] [Preadditive D]
variable [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]

/--
A functor between `R`-linear categories is module-linear over `R` when it is
both additive and `R`-linear, equivalently when each induced map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is an `R`-module homomorphism.
-/
class ModuleLinear (F : C ⥤ D) : Prop extends F.Additive, F.Linear R

/-- The identity functor of an `R`-linear category is module-linear over `R`. -/
instance instModuleLinearId : ModuleLinear R (𝟭 C) :=
  { toAdditive := inferInstance, toLinear := inferInstance }

/--
An additive `R`-linear functor is module-linear over `R`. This is a lemma
rather than an instance, so it cannot loop with the projections from
`ModuleLinear`.
-/
theorem ModuleLinear.ofAdditiveLinear (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ModuleLinear R F :=
  { toAdditive := inferInstance, toLinear := inferInstance }

/--
Module-linearity is the conjunction of additivity and `R`-linearity.
-/
theorem moduleLinear_iff (F : C ⥤ D) :
    ModuleLinear R F ↔ F.Additive ∧ F.Linear R := by
  constructor
  · intro h
    exact ⟨h.toAdditive, h.toLinear⟩
  · rintro ⟨ha, hl⟩
    exact { toAdditive := ha, toLinear := hl }

/-- A functor between preadditive `R`-linear categories is additive and scalar-compatible
if and only if it preserves every expression `r • f + g` on morphisms. -/
theorem additive_linear_iff_map_smul_add (F : C ⥤ D) :
    (F.Additive ∧ Functor.Linear R F) ↔
      ∀ (X Y : C) (r : R) (f g : X ⟶ Y),
        F.map (r • f + g) = r • F.map f + F.map g := by
  constructor
  · rintro ⟨ha, hl⟩
    letI : F.Additive := ha
    letI : F.Linear R := hl
    intro X Y r f g
    rw [F.map_add, F.map_smul]
  · intro h
    have ha : F.Additive := ⟨fun {X Y f g} => by simpa using h X Y 1 f g⟩
    letI : F.Additive := ha
    refine ⟨ha, ⟨fun {X Y} f r => ?_⟩⟩
    simpa using h X Y r f 0

section

variable {R : Type uR} [CommRing R]

/--
The forgetful functor from finitely generated `R`-modules to all `R`-modules
is module-linear over `R`.
-/
instance instModuleLinearForget₂FGModuleCat :
    ModuleLinear R (forget₂ (FGModuleCat.{uR} R) (ModuleCat.{uR} R)) :=
  { toAdditive := inferInstance, toLinear := inferInstance }

end

end CategoryTheory.Functor
