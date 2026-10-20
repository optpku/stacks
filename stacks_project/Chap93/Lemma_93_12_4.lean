/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Exal
import StacksCheckRecall

universe u

/- Lemma 93.12.4
For a finite type algebra over a field, smooth outside the closed subset of an
ideal, completion induces a canonical bijection on first-order extensions with
finite coefficients.
-/
@[stacks 0DZ4] #check (Algebra.Exal.adicCompletion_bijective :
  ∀ (k B N : Type u) [Field k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N] [Algebra.FiniteType k B] [Module.Finite B N]
    (J : Ideal B),
    (PrimeSpectrum.zeroLocus (J : Set B))ᶜ ⊆ Algebra.smoothLocus k B →
    Function.Bijective (Algebra.Exal.adicCompletionOfFiniteType k B N J))
