module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import ReasLib.RingTheory.Flatness.Tor
public import ReasLib.RingTheory.Ideal.Tensor

/-!
# Flatness over Artinian local rings

This leaf owns the quotient criterion in the Artinian local case.  Its canonical form uses
injectivity of ideal tensor multiplication and is universe-polymorphic; the same-universe `Tor₁`
form is retained as the source-facing bridge.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Pointwise

universe u v

namespace Module.Flat.ArtinianLocal

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]

section Tensor

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Stacks `051K`, ideal-tensor form: over an Artinian local ring, flatness is equivalent to
quotient flatness and injectivity of multiplication `I ⊗[R] M → M` for any proper ideal `I`. -/
@[stacks 051K "ideal tensor form"]
theorem iff_quotient_flat_and_tensorMul_injective (I : Ideal R) (hI : I ≠ ⊤) :
    Module.Flat R M ↔
      Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) ∧
        Function.Injective (I.tensorMul M) := sorry

end Tensor

section Tor

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Lemma 10.101.6 (Stacks `051K`): for a proper ideal of an Artinian local ring, flatness is
detected by flatness of the quotient module and vanishing of the first `Tor`. -/
@[stacks 051K]
theorem iff_quotient_flat_and_tor_one (I : Ideal R) (hI : I ≠ ⊤) :
    Module.Flat R M ↔
      Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) ∧
        IsZero (Tor₁[R](R ⧸ I, M)) := sorry

end Tor

end Module.Flat.ArtinianLocal
