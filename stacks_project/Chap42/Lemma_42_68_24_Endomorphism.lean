module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ModuleEnd

/-!
# Compatibility bridge for two-periodic complexes from module endomorphisms

The reusable constructor is owned by its mathematical ReasLib module.
-/

@[expose] public section

open CategoryTheory

universe u v

#check (CategoryTheory.TwoPeriodicEndomorphism.ofModuleEnd :
  {R : Type u} → [Ring R] → {M : Type v} → [AddCommGroup M] → [Module R M] →
    (phi psi : Module.End R M) → phi.range ≤ psi.ker → psi.range ≤ phi.ker →
      CategoryTheory.TwoPeriodicEndomorphism (ModuleCat R))
