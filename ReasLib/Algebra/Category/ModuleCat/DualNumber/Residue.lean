/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Epsilon
public import ReasLib.RingTheory.DualNumber.Residue

@[expose] public section

/-!
# The residue module of the dual numbers

This file owns the module-level data used by periodic resolutions over the dual
numbers.  Homological constructions belong in downstream files.

@stack 0A5Q
@stack 0A5U
-/

noncomputable section

universe u

open CategoryTheory
open scoped DualNumber

namespace DualNumber

variable (k : Type u) [CommRing k]

/-- The residue module `k[ε] / (ε)` over the dual numbers. -/
@[stacks 0A5Q "the residue module of the dual numbers",
  stacks 0A5U "the residue module of the dual numbers"]
abbrev residueModule : ModuleCat k[ε] :=
  ModuleCat.of k[ε] (k[ε] ⧸ epsIdeal k)

/-- Multiplication by `ε` as an endomorphism of the regular dual-number module. -/
@[stacks 0A5Q "multiplication by epsilon", stacks 0A5U "multiplication by epsilon"]
def epsEnd :
    ModuleCat.of k[ε] k[ε] ⟶ ModuleCat.of k[ε] k[ε] :=
  ModuleCat.DualNumber.epsEnd (ModuleCat.of k[ε] k[ε])

/-- The quotient map from the regular dual-number module to its residue module. -/
@[stacks 0A5Q "dual-number residue quotient", stacks 0A5U "dual-number residue quotient"]
def residueQuotient :
    ModuleCat.of k[ε] k[ε] ⟶ residueModule k :=
  ModuleCat.ofHom
    (Ideal.Quotient.mkₐ k[ε] (epsIdeal k)).toLinearMap

/-- Multiplication by `ε` keeps precisely the scalar coefficient in the square-zero direction. -/
theorem epsEnd_apply (x : k[ε]) :
    (epsEnd k).hom x = TrivSqZeroExt.inr x.fst := by
  change (ε : k[ε]) * x = TrivSqZeroExt.inr x.fst
  ext <;> simp

/-- Multiplication by `ε` is square-zero. -/
theorem epsEnd_sq : epsEnd k ≫ epsEnd k = 0 :=
  ModuleCat.DualNumber.epsEnd_sq (ModuleCat.of k[ε] k[ε])

/-- The range of multiplication by `ε` is the ideal `(ε)`. -/
theorem range_epsEnd :
    LinearMap.range (epsEnd k).hom = epsIdeal k := by
  ext x
  change (∃ y, (epsEnd k).hom y = x) ↔ x ∈ TrivSqZeroExt.kerIdeal k k
  rw [TrivSqZeroExt.mem_kerIdeal_iff_inr]
  constructor
  · rintro ⟨y, rfl⟩
    rw [epsEnd_apply k y]
    rfl
  · intro hx
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    rw [epsEnd_apply k (TrivSqZeroExt.inl x.snd)]
    exact hx.symm

/-- The kernel of multiplication by `ε` is the ideal `(ε)`. -/
theorem ker_epsEnd :
    LinearMap.ker (epsEnd k).hom = epsIdeal k := by
  ext x
  change (epsEnd k).hom x = 0 ↔ x.fst = 0
  rw [epsEnd_apply]
  constructor
  · intro hx
    simpa using congrArg TrivSqZeroExt.snd hx
  · intro hx
    rw [hx, TrivSqZeroExt.inr_zero]

/-- Multiplication by `ε` has equal range and kernel. -/
theorem range_epsEnd_eq_ker :
    LinearMap.range (epsEnd k).hom = LinearMap.ker (epsEnd k).hom := by
  rw [range_epsEnd, ker_epsEnd]

/-- The kernel of the residue quotient is the ideal `(ε)`. -/
theorem ker_residueQuotient :
    LinearMap.ker (residueQuotient k).hom = epsIdeal k := by
  ext x
  change Ideal.Quotient.mk (epsIdeal k) x = 0 ↔ x ∈ epsIdeal k
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Multiplication by `ε` followed by the residue quotient is zero. -/
theorem epsEnd_comp_residueQuotient :
    epsEnd k ≫ residueQuotient k = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (residueQuotient k).hom ((epsEnd k).hom x) = 0
  apply (LinearMap.mem_ker).mp
  rw [ker_residueQuotient, ← range_epsEnd]
  exact LinearMap.mem_range_self _ x

end DualNumber
