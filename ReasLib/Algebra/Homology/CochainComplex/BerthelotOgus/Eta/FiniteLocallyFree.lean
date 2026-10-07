module

public import ReasLib.Algebra.Homology.CochainComplex.Nat.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.DeterminantalIdeal
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Pair.Exact
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
public import ReasLib.RingTheory.Flatness.LocallyFree

/-!
# Finite local freeness of terms of the eta complex

A principal eta determinantal ideal controls the corresponding term of the nonnegative
Berthelot-Ogus eta complex.  Only the two terms entering the degreewise presentation are assumed
finite free.
@stack 0F7W
-/

@[expose] public section

open CategoryTheory
open scoped BerthelotOgus nonZeroDivisors

universe u v

namespace CochainComplex.BerthelotOgus.Nat

variable {A : Type u} [CommRing A]

/-- A principal eta determinantal ideal makes the corresponding eta term finite locally free of
the expected rank; only the two terms in the degreewise presentation are needed. -/
theorem term_finiteLocallyFreeOfRank_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A) (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    Module.FiniteLocallyFreeOfRank A ((η[f] K).X i) (Module.finrank A (K.X i)) := sorry

/-- Lemma 15.97.5 (1), Tag 0F7W: the bounded finite-free specialization of
`term_finiteLocallyFreeOfRank_of_isPrincipal`. -/
@[stacks 0F7W "finite local freeness of a Berthelot-Ogus eta term"]
theorem term_finiteLocallyFreeOfRank
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    (hK : CochainComplex.Nat.IsBoundedAbove K)
    [CochainComplex.Nat.IsTermwiseFiniteFree K]
    (hf : f ∈ nonZeroDivisors A) (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    Module.FiniteLocallyFreeOfRank A ((η[f] K).X i) (Module.finrank A (K.X i)) := sorry

namespace Pair

/-- Under the same degreewise principal-ideal hypothesis, the visible-power pair map of the eta
term is a split monomorphism. -/
theorem pairLinear_isSplitMono_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A) (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsSplitMono (ModuleCat.ofHom (pairLinear f K i)) := sorry

/-- Lemma 15.97.5 (2), Tag 0F7W: the bounded finite-free specialization of
`pairLinear_isSplitMono_of_isPrincipal`. -/
@[stacks 0F7W "split visible-power pair map for a Berthelot-Ogus eta term"]
theorem pairLinear_isSplitMono
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (i : ℕ)
    (hK : CochainComplex.Nat.IsBoundedAbove K)
    [CochainComplex.Nat.IsTermwiseFiniteFree K]
    (hf : f ∈ nonZeroDivisors A) (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsSplitMono (ModuleCat.ofHom (pairLinear f K i)) := sorry

end Pair

end CochainComplex.BerthelotOgus.Nat
