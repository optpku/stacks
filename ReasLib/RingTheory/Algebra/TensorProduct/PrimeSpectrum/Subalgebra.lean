/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Polynomial
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

@[expose] public section

/-!
# Spectral Images of Tensor Subalgebras

@stack 037F

Localizing a tensor product at an element from a tensor subalgebra does not change its image on
the spectrum of the right tensor factor.
-/

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w

namespace Algebra.TensorProduct

/-- Lemma 10.41.9: if `S'` is a `k`-subalgebra of `S` and `f ∈ S' ⊗[k] R`, then the localized
maps from `S' ⊗[k] R` and `S ⊗[k] R` have the same image in `Spec R`. -/
@[stacks 037F]
theorem range_comap_localized_subalgebra_eq
    {k : Type u} {R : Type v} {S : Type w} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (S' : Subalgebra k S) (f : S' ⊗[k] R) :
    Set.range
        (PrimeSpectrum.comap
          (algebraMap R
            (Localization.Away
              (Algebra.TensorProduct.map S'.val (AlgHom.id k R) f))) :
          PrimeSpectrum
              (Localization.Away
                (Algebra.TensorProduct.map S'.val (AlgHom.id k R) f)) →
            PrimeSpectrum R) =
      Set.range
        (PrimeSpectrum.comap (algebraMap R (Localization.Away f)) :
          PrimeSpectrum (Localization.Away f) → PrimeSpectrum R) := sorry

end Algebra.TensorProduct
