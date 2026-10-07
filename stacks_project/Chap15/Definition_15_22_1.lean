module

import StacksCheckRecall
public import ReasLib.Algebra.Module.Torsion.Characterizations

/-!
# Definition 15.22.1

The reusable characterizations are owned by `Submodule` and `Module`; this chapter entry fixes the
three source specializations and their universe-polymorphic types.

@stack 0536
-/

@[expose] public section

universe u v

/- @stack 0536 -/
@[stacks 0536 "Definition 15.22.1 (1): torsion elements"]
#check fun (R : Type u) (M : Type v) [CommSemiring R] [IsDomain R]
    [AddCommMonoid M] [Module R M] (x : M) ↦
  (Submodule.mem_torsion_iff_exists_ne_zero_smul_eq_zero (R := R) x :
    x ∈ Submodule.torsion R M ↔ ∃ f : R, f ≠ 0 ∧ f • x = 0)

/- @stack 0536 -/
@[stacks 0536 "Definition 15.22.1 (2): torsion-free modules"]
#check fun (R : Type u) (M : Type v) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] ↦
  (Submodule.isTorsionFree_iff_forall_mem_torsion_eq_zero (R := R) (M := M) :
    Module.IsTorsionFree R M ↔
      ∀ x : M, x ∈ Submodule.torsion R M → x = 0)

/- @stack 0536 -/
@[stacks 0536 "Definition 15.22.1 (3): torsion modules"]
#check fun (R : Type u) (M : Type v) [CommSemiring R]
    [AddCommMonoid M] [Module R M] ↦
  (Module.isTorsion_iff_forall_mem_torsion (R := R) (M := M) :
    Module.IsTorsion R M ↔ ∀ x : M, x ∈ Submodule.torsion R M)

#check @Submodule.torsion
#check @Module.IsTorsionFree
#check @Module.IsTorsion
