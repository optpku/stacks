module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Order.Lattice.Nat
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.RingTheory.Depth.RegularSequence

/-!
# Depth and Residue-Field Ext

This file owns the residue-field Ext profile of a module over a local ring and
the characterization of depth as its first nonvanishing degree.
-/

@[expose] public section

universe u v

open CategoryTheory
open IsLocalRing
open scoped ENat

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The residue-field Ext group `Ext^i_R(ResidueField R, M)`. -/
abbrev ResidueFieldExt (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (i : ℕ) : Type (max u v) :=
  Abelian.Ext (ModuleCat.of R (ULift.{v, u} (ResidueField R)))
    (ModuleCat.of R (ULift.{u, v} M)) i

namespace ResidueFieldExt

/-- The residue-field Ext group of `M` in degree `i` is nonzero. -/
abbrev Nonzero (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (i : ℕ) : Prop :=
  Nontrivial (ResidueFieldExt R M i)

/-- Nonvanishing of a residue-field Ext group is equivalent to containing a
nonzero Ext class. -/
theorem nonzero_iff_exists_ne_zero (i : ℕ) :
    Nonzero R M i ↔ ∃ e : ResidueFieldExt R M i, e ≠ 0 := sorry

/-- The degree-zero residue-field Ext group is nonzero exactly when there is a
nonzero linear map from the residue field. -/
theorem nonzero_zero_iff_exists_ne_zero_linearMap :
    Nonzero R M 0 ↔ ∃ f : ResidueField R →ₗ[R] M, f ≠ 0 := sorry

/-- For a nonzero finite module over a local ring, degree-zero
residue-field Ext is nonzero exactly when the module has depth zero. -/
@[stacks 00LW "depth zero and residue-field Ext"]
theorem nonzero_zero_iff_moduleDepth_eq_zero [Module.Finite R M] [Nontrivial M] :
    Nonzero R M 0 ↔ moduleDepth R M = 0 := sorry

/-- Some residue-field Ext group of a nonzero finite module over a Noetherian
local ring is nonzero. -/
@[stacks 00LW "existence of nonzero residue-field Ext"]
theorem exists_nonzero [IsNoetherianRing R] [Module.Finite R M] [Nontrivial M] :
    ∃ i : ℕ, Nonzero R M i := sorry

/-- The least degree in which the residue-field Ext group of `M` is nonzero.
Existence is part of the input, so the datum has no empty-set fallback. -/
@[stacks 00LW "first nonzero residue-field Ext index"]
noncomputable def firstNonzeroIndex
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] : ℕ :=
  sInf {i : ℕ | Nonzero R M i}

/-- The first nonvanishing residue-field Ext degree is itself nonvanishing for
a nonzero finite module over a Noetherian local ring. -/
theorem firstNonzeroIndex_spec [IsNoetherianRing R]
    [Module.Finite R M] [Nontrivial M] :
    Nonzero R M (firstNonzeroIndex R M) := sorry

/-- Residue-field Ext vanishes in every degree below its first nonvanishing
degree. -/
theorem not_nonzero_of_lt_firstNonzeroIndex [IsNoetherianRing R]
    [Module.Finite R M] [Nontrivial M] {i : ℕ}
    (hi : i < firstNonzeroIndex R M) :
    ¬ Nonzero R M i := sorry

/-- The first nonvanishing residue-field Ext degree is at most every degree in
which residue-field Ext is nonzero. -/
theorem firstNonzeroIndex_le [IsNoetherianRing R] [Module.Finite R M]
    [Nontrivial M] {i : ℕ} (hi : Nonzero R M i) :
    firstNonzeroIndex R M ≤ i := sorry

/-- A natural number is the first nonvanishing residue-field Ext degree exactly
when Ext is nonzero there and vanishes in every smaller degree. -/
theorem firstNonzeroIndex_eq_iff [IsNoetherianRing R]
    [Module.Finite R M] [Nontrivial M] {n : ℕ} :
    firstNonzeroIndex R M = n ↔
      Nonzero R M n ∧ ∀ i < n, ¬ Nonzero R M i := sorry

/-- If a nonzero finite module has depth `n`, its residue-field Ext is nonzero
in degree `n` and vanishes in every smaller degree. -/
theorem profile_of_moduleDepth_eq [IsNoetherianRing R]
    [Module.Finite R M] [Nontrivial M] {n : ℕ}
    (hdepth : moduleDepth R M = n) :
    Nonzero R M n ∧ ∀ i < n, ¬ Nonzero R M i := sorry

/-- Lemma 10.72.5, tag `00LW`: the depth of a nonzero finite module over a
Noetherian local ring is the first degree in which its residue-field Ext group
is nonzero. -/
@[stacks 00LW]
theorem moduleDepth_eq_firstNonzeroIndex [IsNoetherianRing R]
    [Module.Finite R M] [Nontrivial M] :
    moduleDepth R M = (firstNonzeroIndex R M : ℕ∞) := sorry

end ResidueFieldExt

/-- A finite module of depth zero over a local ring contains a nonzero element annihilated by the
maximal ideal. -/
@[stacks 00LW "annihilated element at depth zero"]
theorem exists_nonzero_annihilated_by_maximalIdeal_of_depth_zero
    [Module.Finite R M] (hdepth : moduleDepth R M = 0) :
    ∃ m : M, m ≠ 0 ∧ ∀ r ∈ maximalIdeal R, r • m = 0 := sorry

end Module

namespace IsLocalRing

/-- Every element of the maximal ideal annihilates the residue field. -/
theorem smul_residueField_eq_zero_of_mem_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (y : ResidueField R) :
    x • y = 0 := sorry

end IsLocalRing

/-- Deprecated compatibility spelling for `Module.maximalIdeal_smul_top_ne_top`. -/
@[deprecated Module.maximalIdeal_smul_top_ne_top (since := "2026-08-04")]
theorem maximalIdeal_smul_top_ne_top
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := sorry

/-- Deprecated compatibility spelling for
`Module.moduleDepth_eq_zero_iff_no_isSMulRegular`. -/
@[deprecated Module.moduleDepth_eq_zero_iff_no_isSMulRegular (since := "2026-08-04")]
theorem moduleDepth_eq_zero_iff_no_maximalIdeal_regular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    moduleDepth R M = 0 ↔ ¬ ∃ x ∈ maximalIdeal R, IsSMulRegular M x := sorry

/-- Deprecated compatibility spelling for
`Module.exists_isSMulRegular_of_moduleDepth_ne_zero`. -/
@[deprecated Module.exists_isSMulRegular_of_moduleDepth_ne_zero (since := "2026-08-04")]
theorem exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hdepth : moduleDepth R M ≠ 0) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x := sorry

/-- Deprecated compatibility spelling for
`Module.exists_isRegular_of_moduleDepth_eq`. -/
@[deprecated Module.exists_isRegular_of_moduleDepth_eq (since := "2026-08-04")]
theorem exists_regularSequence_of_length_eq_moduleDepth
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    {n : ℕ} (hdepth : moduleDepth R M = n) :
    ∃ rs : List R, RingTheory.Sequence.IsRegular M rs ∧
      Ideal.ofList rs ≤ maximalIdeal R ∧ rs.length = n := sorry
