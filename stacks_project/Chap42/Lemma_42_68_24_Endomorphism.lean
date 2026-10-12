/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
