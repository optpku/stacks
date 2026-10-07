module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Module-linear functors

A functor between `R`-linear categories is module-linear over `R` when it is both
additive and `R`-linear, so each induced map on hom-modules is an `R`-module
homomorphism.
-/

@[expose] public section

universe u v w v₁ v₂

open CategoryTheory

variable (R : Type u) [Semiring R]
variable {C : Type v} {D : Type w}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [Preadditive C] [Preadditive D]
variable [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]

namespace CategoryTheory.Functor

/-- A functor between `R`-linear categories is module-linear over `R` when it is
both additive and `R`-linear, equivalently when each induced map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is an `R`-module homomorphism. -/
class ModuleLinear (F : C ⥤ D) : Prop extends F.Additive, F.Linear R

/-- The identity functor of an `R`-linear category is module-linear over `R`. -/
instance instModuleLinearId : ModuleLinear R (𝟭 C) := sorry

/-- An additive `R`-linear functor is module-linear over `R`. This is a lemma
rather than an instance, so it cannot loop with the projections from
`ModuleLinear`. -/
theorem ModuleLinear.ofAdditiveLinear (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ModuleLinear R F := sorry

/-- Module-linearity is the conjunction of additivity and `R`-linearity. -/
theorem moduleLinear_iff (F : C ⥤ D) :
    ModuleLinear R F ↔ F.Additive ∧ F.Linear R := sorry

section

variable {R : Type u} [CommRing R]

/-- The forgetful functor from finitely generated `R`-modules to all `R`-modules
is module-linear over `R`. -/
instance instModuleLinearForget₂FGModuleCat :
    ModuleLinear R (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) := sorry

end

end CategoryTheory.Functor
