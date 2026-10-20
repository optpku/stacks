/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0565
# Torsion detected by principal-open localization families

The principal-open Cech family map detects elements annihilated by powers of
the chosen denominators.  For a finite family, its injectivity is equivalent
to vanishing of the submodule annihilated by every denominator.  This leaf
also names the coordinatewise scalar-multiplication map used in that finite
reduction.
-/

@[expose] public section

universe u v w

namespace LocalizedModule.Away.Cech

variable {R : Type u} {ι : Type w}

/-- The coordinatewise scalar-multiplication map associated to a family of
elements of a commutative semiring. -/
@[stacks 0565 "scalar-multiplication family map"]
def smulFamilyMap [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M]
    (f : ι → R) : M →ₗ[R] (ι → M) :=
  LinearMap.pi fun i ↦ DistribSMul.toLinearMap R M (f i)

/-- The `i`-th component of `smulFamilyMap M f m` is `f i • m`. -/
@[simp, stacks 0565 "scalar-multiplication family map application"]
theorem smulFamilyMap_apply [CommSemiring R]
    (M : Type v) [AddCommMonoid M] [Module R M]
    (f : ι → R) (m : M) (i : ι) :
    smulFamilyMap M f m i = f i • m := sorry

/-- The kernel of the scalar-multiplication family map is exactly the
submodule annihilated by every member of the family. -/
@[stacks 0565 "kernel of the scalar-multiplication family map"]
theorem ker_smulFamilyMap [CommSemiring R]
    (M : Type v) [AddCommMonoid M] [Module R M] (f : ι → R) :
    LinearMap.ker (smulFamilyMap M f) =
      Submodule.torsionBySet R M (Set.range f) := sorry

/-- An element maps to zero in every principal-open localization exactly when
some positive power of each corresponding denominator annihilates it. -/
@[stacks 0565 "principal-open family-map zero criterion"]
theorem familyMap_apply_eq_zero_iff_exists_pow_smul_eq_zero
    [CommRing R] (M : Type v) [AddCommMonoid M] [Module R M]
    (f : ι → R) (m : M) :
    familyMap M f m = 0 ↔
      ∀ i, ∃ e : ℕ, 0 < e ∧ (f i) ^ e • m = 0 := sorry

/-- For a finite family, the principal-open family map is injective exactly
when the common scalar-torsion submodule vanishes. -/
@[stacks 0565 "principal-open family-map injectivity via torsion"]
theorem familyMap_injective_iff_torsionBySet_eq_bot
    [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] [Finite ι]
    (f : ι → R) :
    Function.Injective (familyMap M f) ↔
      Submodule.torsionBySet R M (Set.range f) = ⊥ := sorry

/-- For a finite family, localization-family injectivity is equivalent to
injectivity of the coordinatewise scalar-multiplication map. -/
@[stacks 0565 "localization and scalar-family injectivity comparison"]
theorem familyMap_injective_iff_smulFamilyMap_injective
    [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] [Finite ι]
    (f : ι → R) :
    Function.Injective (familyMap M f) ↔
      Function.Injective (smulFamilyMap M f) := sorry

end LocalizedModule.Away.Cech
