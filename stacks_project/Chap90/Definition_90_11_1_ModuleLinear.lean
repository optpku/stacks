module

public import ReasLib.CategoryTheory.Linear.Functor

/-!
# Module-linear functors

A functor between `R`-linear categories is module-linear over `R` when it is both
additive and `R`-linear, so each induced map on hom-modules is an `R`-module
homomorphism.
-/

@[expose] public section

universe u v w v₁ v₂

open CategoryTheory

variable (R : Type u) [CommRing R]
variable {C : Type v} {D : Type w}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [Preadditive C] [Preadditive D]
variable [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]

/-
The promoted module-linearity interface remains available through the
source-facing chapter module.
-/
#check (CategoryTheory.Functor.ModuleLinear R (𝟭 C) : Prop)

/-
The promoted additive-and-linear constructor remains available through the
source-facing chapter module.
-/
#check (CategoryTheory.Functor.ModuleLinear.ofAdditiveLinear (R := R)
  (F := 𝟭 C) : CategoryTheory.Functor.ModuleLinear R (𝟭 C))

/-
The promoted characterization of module-linearity remains available through
the source-facing chapter module.
-/
#check (CategoryTheory.Functor.moduleLinear_iff R (𝟭 C) :
  CategoryTheory.Functor.ModuleLinear R (𝟭 C) ↔
    (𝟭 C).Additive ∧ (𝟭 C).Linear R)

/-
The promoted finitely generated-module specialization remains available
through the source-facing chapter module.
-/
#check (CategoryTheory.Functor.instModuleLinearForget₂FGModuleCat (R := R) :
  CategoryTheory.Functor.ModuleLinear R
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)))
