/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.DeterminantalIdeal
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Pair
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
public import ReasLib.RingTheory.Flatness.LocallyFree

/-!
# Finite local freeness of integer-indexed eta terms

The divided-coordinate model makes the degree-local content independent of visible integer
powers.  Principality of the eta determinantal ideal controls finite local freeness and splitting
of the canonical pair in every integer degree.

@stack 0F7W
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u v

namespace CochainComplex.BerthelotOgus.Int

variable {A : Type u} [CommRing A]

/-- A nonzerodivisor acts regularly on a termwise finite-free integer cochain complex. -/
theorem termwiseTorsionFree
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    [K.IsTermwiseFiniteFree] (hf : f ∈ nonZeroDivisors A) :
    IsTermwiseTorsionFree f K := sorry

/-- A termwise finite-free complex, bundled in the canonical eta domain of a
nonzerodivisor. -/
@[stacks 0F7W "finite-free object of the integer eta domain"]
def finiteFreeDomain
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    [K.IsTermwiseFiniteFree] : Domain (f : A) :=
  ⟨K, termwiseTorsionFree (f : A) K f.property⟩

/-- A principal eta determinantal ideal makes the corresponding divided-coordinate eta term
finite locally free of the expected rank. -/
theorem term_finiteLocallyFreeOfRank_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    Module.FiniteLocallyFreeOfRank A (term f K i) (Module.finrank A (K.X i)) := sorry

/-- Lemma 15.97.5 (1), Tag 0F7W: every term of the eta complex of a bounded finite-free
complex is finite locally free when the corresponding determinantal ideal is principal. -/
@[stacks 0F7W "finite local freeness of an integer-indexed eta term"]
theorem term_finiteLocallyFreeOfRank
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : CochainComplex.bounded (ModuleCat.{v} A) K) [K.IsTermwiseFiniteFree]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    Module.FiniteLocallyFreeOfRank A (term f K i) (Module.finrank A (K.X i)) := sorry

namespace Pair

/-- Under the degree-local principal-ideal hypothesis, the canonical-domain
divided-coordinate pair is a split monomorphism. -/
theorem linear_isSplitMono
    (f : A) (K : Domain f) (i : ℤ)
    [Module.Free A (K.obj.X i)] [Module.Finite A (K.obj.X i)]
    [Module.Free A (K.obj.X (i + 1))] [Module.Finite A (K.obj.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (etaDeterminantalIdeal f K.obj i).IsPrincipal) :
    IsSplitMono (ModuleCat.ofHom (linear f K i)) := sorry

/-- Under the degree-local principal-ideal hypothesis, the divided-coordinate eta pair is a
split monomorphism. -/
theorem pairLinear_isSplitMono_of_isPrincipal
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hreg : IsTermwiseTorsionFree f K)
    [Module.Free A (K.X i)] [Module.Finite A (K.X i)]
    [Module.Free A (K.X (i + 1))] [Module.Finite A (K.X (i + 1))]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsSplitMono (ModuleCat.ofHom (pairLinear f K i hreg)) := sorry

/-- Lemma 15.97.5 (2), Tag 0F7W: the canonical divided-coordinate pair of a bounded
finite-free eta complex is split under the principal-ideal hypothesis. -/
@[stacks 0F7W "split integer-indexed Berthelot-Ogus eta pair"]
theorem pairLinear_isSplitMono
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : CochainComplex.bounded (ModuleCat.{v} A) K) [K.IsTermwiseFiniteFree]
    (hf : f ∈ nonZeroDivisors A)
    (hI : (etaDeterminantalIdeal f K i).IsPrincipal) :
    IsSplitMono
      (ModuleCat.ofHom (pairLinear f K i (termwiseTorsionFree f K hf))) := sorry

end Pair

end CochainComplex.BerthelotOgus.Int
