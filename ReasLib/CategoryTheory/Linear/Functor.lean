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
instance instModuleLinearId : ModuleLinear R (𝟭 C) := sorry

/--
An additive `R`-linear functor is module-linear over `R`. This is a lemma
rather than an instance, so it cannot loop with the projections from
`ModuleLinear`.
-/
theorem ModuleLinear.ofAdditiveLinear (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ModuleLinear R F := sorry

/--
Module-linearity is the conjunction of additivity and `R`-linearity.
-/
theorem moduleLinear_iff (F : C ⥤ D) :
    ModuleLinear R F ↔ F.Additive ∧ F.Linear R := sorry

/-- A functor between preadditive `R`-linear categories is additive and scalar-compatible
if and only if it preserves every expression `r • f + g` on morphisms. -/
theorem additive_linear_iff_map_smul_add (F : C ⥤ D) :
    (F.Additive ∧ Functor.Linear R F) ↔
      ∀ (X Y : C) (r : R) (f g : X ⟶ Y),
        F.map (r • f + g) = r • F.map f + F.map g := sorry

section

variable {R : Type uR} [CommRing R]

/--
The forgetful functor from finitely generated `R`-modules to all `R`-modules
is module-linear over `R`.
-/
instance instModuleLinearForget₂FGModuleCat :
    ModuleLinear R (forget₂ (FGModuleCat.{uR} R) (ModuleCat.{uR} R)) := sorry

end

end CategoryTheory.Functor
