/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPowerSeries.Hypersurface
import StacksCheckRecall

/-!
# Finite-dimensionality of Inf and T for power-series hypersurfaces

For `P = MvPowerSeries (Fin n) k ⧸ Ideal.span {f}` as in Lemma 93.8.3, finite-dimensionality
of `Inf(Def_P)` and `T Def_P` is stated on the identified spaces `Derivation k P P` and
`extOneNaiveCotangent k P P`.
-/

@[expose] public section

universe u

open IsLocalRing
open RingHom.SquareZeroExtension

/- Lemma 93.8.11 (1)
In Lemma 93.8.3, if `P = MvPowerSeries (Fin n) k ⧸ Ideal.span {f}` for nonzero
`f ∈ maximalIdeal (MvPowerSeries (Fin n) k) ^ 2`, then `Inf(Def_P)` is finite-dimensional
over `k` if and only if `n = 1`. Via Lemma 93.8.3, `Inf(Def_P)` is identified with
`Derivation k P P`. -/
@[stacks 0DY5] #check
  (MvPowerSeries.Hypersurface.finiteDimensional_derivation_iff :
    ∀ {k : Type u} [Field k] {n : ℕ}
    (f : MvPowerSeries (Fin n) k) (hf_ne : f ≠ 0)
    (hf_sq : f ∈ maximalIdeal (MvPowerSeries (Fin n) k) ^ 2),
    let P := MvPowerSeries (Fin n) k ⧸ Ideal.span {f}
    FiniteDimensional k (Derivation k P P) ↔ n = 1)

/- Lemma 93.8.11 (2)
In Lemma 93.8.3, in the same setup, `T Def_P` is finite-dimensional over `k` if
`Ideal.radical (Ideal.span ({f} ∪ Set.range fun i ↦ MvPowerSeries.partialDeriv i f))`
equals `maximalIdeal (MvPowerSeries (Fin n) k)`. Via Lemma 93.8.3, `T Def_P` is identified
with `extOneNaiveCotangent k P P`. -/
@[stacks 0DY5] #check
  (MvPowerSeries.Hypersurface.finiteDimensional_extOneNaiveCotangent :
    ∀ {k : Type u} [Field k] {n : ℕ}
    (f : MvPowerSeries (Fin n) k) (hf_ne : f ≠ 0)
    (hf_sq : f ∈ maximalIdeal (MvPowerSeries (Fin n) k) ^ 2)
    (hjac :
      Ideal.radical
          (Ideal.span ({f} ∪ Set.range fun i : Fin n ↦ MvPowerSeries.partialDeriv i f)) =
        maximalIdeal (MvPowerSeries (Fin n) k)),
    let P := MvPowerSeries (Fin n) k ⧸ Ideal.span {f}
    FiniteDimensional k (extOneNaiveCotangent k P P))
