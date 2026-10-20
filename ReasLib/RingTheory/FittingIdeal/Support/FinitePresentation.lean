module

public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FittingIdeal.FinitePresentation
public import ReasLib.RingTheory.FittingIdeal.Support

/-!
# Support of finitely presented modules

The zeroth Fitting ideal presents the support as a closed subset. Finite
presentation makes that ideal finitely generated, so the complementary open
is compact.

@stack 051B
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.40.8 (Stacks tag `051B`): the support of a finitely presented
module is closed and its complement is compact. -/
@[stacks 051B]
theorem isClosed_support_and_isCompact_compl_support
    [Module.FinitePresentation R M] :
    IsClosed (support R M) ∧ IsCompact (support R M)ᶜ := by
  refine ⟨Module.isClosed_support, ?_⟩
  rw [← zeroLocus_fittingIdeal_zero_eq_support (R := R) (M := M)]
  exact ((PrimeSpectrum.isCompact_isOpen_iff_ideal (R := R)).mpr
    ⟨fittingIdeal R M 0, Module.FinitePresentation.fittingIdeal_fg 0, rfl⟩).1

end Module
