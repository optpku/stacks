/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Length
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
public import ReasLib.RingTheory.Ideal.HilbertSamuel
public import ReasLib.RingTheory.Ideal.OfDefinition
public import ReasLib.RingTheory.LocalRing.Quotient

/-!
# Finiteness of Hilbert--Samuel Quotients

@stack 00K5
@stack 07DU

This file isolates the finiteness facts behind Hilbert--Samuel functions.  The
primary API is stated for an Artinian quotient; ideals of definition provide a
source-facing specialization in a Noetherian local ring.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The Hilbert--Samuel function satisfies the usual successive-quotient
recurrence before any finiteness assumption is imposed. -/
theorem hilbertSamuelChi_succ (I : Ideal R) (n : ℕ) :
    hilbertSamuelChi I M (n + 1) =
      hilbertSamuelChi I M n + hilbertSamuelPhi I M (n + 1) := sorry

/-- If `R ⧸ I` is Artinian, the adic quotients of a finite module over a
Noetherian ring have finite length over `R`. -/
theorem isFiniteLength_hilbertSamuelQuotient
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] (n : ℕ) :
    IsFiniteLength R
      (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := sorry

/-- If `R ⧸ I` is Artinian, every associated Hilbert--Samuel graded piece of
a finite module over a Noetherian ring has finite length over `R`. -/
theorem isFiniteLength_hilbertSamuelGradedPiece
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] (n : ℕ) :
    IsFiniteLength R (Ideal.AssociatedGraded.piece I M n) := sorry

/-- Under the finite Artinian-quotient hypotheses, every Hilbert--Samuel
`χ`-value is finite. -/
theorem hilbertSamuelChi_ne_top
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] (n : ℕ) :
    hilbertSamuelChi I M n ≠ ⊤ := sorry

/-- Under the finite Artinian-quotient hypotheses, every Hilbert--Samuel
`φ`-value is finite. -/
theorem hilbertSamuelPhi_ne_top
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] (n : ℕ) :
    hilbertSamuelPhi I M n ≠ ⊤ := sorry

/-- The zeroth Hilbert--Samuel value is the length of the first adic quotient.
This data-level identity is useful independently of locality or finiteness. -/
theorem hilbertSamuelChi_zero (I : Ideal R) :
    hilbertSamuelChi I M 0 =
      Module.length R (M ⧸ (I • (⊤ : Submodule R M))) := sorry

/-- The zeroth Hilbert--Samuel value after conversion to natural numbers. -/
theorem hilbertSamuelChi_zero_toNat (I : Ideal R) :
    (hilbertSamuelChi I M 0).toNat =
      (Module.length R (M ⧸ (I • (⊤ : Submodule R M)))).toNat := sorry

/-- The successor recurrence for Hilbert--Samuel lengths can be converted to
natural numbers as soon as the two terms on the right are finite. -/
theorem hilbertSamuelChi_succ_toNat_of_ne_top
    (I : Ideal R) (n : ℕ)
    (h_chi : hilbertSamuelChi I M n ≠ ⊤)
    (h_phi : hilbertSamuelPhi I M (n + 1) ≠ ⊤) :
    (hilbertSamuelChi I M (n + 1)).toNat =
      (hilbertSamuelChi I M n).toNat +
        (hilbertSamuelPhi I M (n + 1)).toNat := sorry

/-- For a finite module over an Artinian quotient, the successor recurrence for
Hilbert--Samuel lengths remains valid after conversion from `ℕ∞` to `ℕ`. -/
theorem hilbertSamuelChi_succ_toNat
    [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] (n : ℕ) :
    (hilbertSamuelChi I M (n + 1)).toNat =
      (hilbertSamuelChi I M n).toNat +
        (hilbertSamuelPhi I M (n + 1)).toNat := sorry

variable [hLocal : IsLocalRing R] [hNoetherian : IsNoetherianRing R]
include hLocal hNoetherian

/-- The quotient by an ideal of definition in a Noetherian local ring is
Artinian. -/
@[stacks 07DU "Artinian quotient by an ideal of definition"]
theorem isArtinianRing_quotient_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) :
    IsArtinianRing (R ⧸ I) := sorry

variable [hFinite : Module.Finite R M]
include hFinite

/-- Every Hilbert--Samuel quotient associated with an ideal of definition has
finite length. -/
theorem isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    IsFiniteLength R
      (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := sorry

/-- Every Hilbert--Samuel graded piece associated with an ideal of definition
has finite length. -/
theorem isFiniteLength_hilbertSamuelGradedPiece_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    IsFiniteLength R (Ideal.AssociatedGraded.piece I M n) := sorry

/-- Every Hilbert--Samuel `χ`-value associated with an ideal of definition is
finite. -/
theorem hilbertSamuelChi_ne_top_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    hilbertSamuelChi I M n ≠ ⊤ := sorry

/-- Every Hilbert--Samuel `φ`-value associated with an ideal of definition is
finite. -/
theorem hilbertSamuelPhi_ne_top_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    hilbertSamuelPhi I M n ≠ ⊤ := sorry

/-- For an ideal of definition, the finite Hilbert--Samuel lengths satisfy the
successor recurrence after conversion to natural numbers. -/
theorem hilbertSamuelChi_succ_toNat_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    (hilbertSamuelChi I M (n + 1)).toNat =
      (hilbertSamuelChi I M n).toNat +
        (hilbertSamuelPhi I M (n + 1)).toNat := sorry

/-- At a positive index, finite Hilbert--Samuel lengths satisfy the usual
first-difference identity after conversion to `ℚ`. -/
theorem hilbertSamuelChi_toNat_eq_hilbertSamuelPhi_toNat_add_pred_of_pos
    (I : Ideal R) (hI : I.IsIdealOfDefinition) {n : ℕ} (hn : 0 < n) :
    ((hilbertSamuelChi I M n).toNat : ℚ) =
      ((hilbertSamuelPhi I M n).toNat : ℚ) +
        ((hilbertSamuelChi I M (n - 1)).toNat : ℚ) := sorry

namespace HilbertSamuel

/-- For a finite-colength submodule, the Hilbert--Samuel `χ`-function is eventually
squeezed between the corresponding submodule function and its translate by the quotient
length. -/
@[stacks 00K5 "finite-colength Hilbert-Samuel bounds"]
theorem exists_eventually_chi_bounds
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hquot : IsFiniteLength R (M ⧸ N)) :
    ∃ c : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      Module.length R (M ⧸ N) + hilbertSamuelChi I N (n - c) ≤
          hilbertSamuelChi I M n ∧
        hilbertSamuelChi I M n ≤
          Module.length R (M ⧸ N) + hilbertSamuelChi I N n := sorry

end HilbertSamuel

end Ideal
