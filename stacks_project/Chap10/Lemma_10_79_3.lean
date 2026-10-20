/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.Free
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.79.3
@stack 0GWM
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
* primary domain: localization descent for free finitely presented modules.
* sampled owner declarations:
  `Module.FinitePresentation.exists_free_localizedModule_powers`,
  `Module.freeLocus`,
  `Module.isOpen_freeLocus`.
* best owner abstraction: the canonical localized module map
  `LocalizedModule.mkLinearMap p.primeCompl M`; freeness after localization at a submonoid is the
  primitive owner statement, while primewise and open-locus formulations are derived views.
* layer: `bridge/view`; this item specializes the submonoid owner theorem to the complement of the
  prime ideal `p` and rewrites membership in `p.primeCompl` as the source-facing condition `f ∉ p`.
* primitive data: `M` and its canonical localization map at `p.primeCompl`.
* derived API: the witness `f ∉ p` and the away-localized freeness statement.
-/

-- Proof sketch: apply `Module.FinitePresentation.exists_free_localizedModule_powers` to the
-- canonical localization map `M → M_p` for the submonoid `p.primeCompl`. Since `M_p` is free, this
-- yields some `f ∈ p.primeCompl` such that `M` localized at the powers of `f` is free. Rewriting
-- `f ∈ p.primeCompl` as `f ∉ p` and the powers-localization as localization away from `f` gives
-- the stated result.
/- Lemma 10.79.3: if a finitely presented `R`-module becomes free after localizing at the prime
ideal `p`, then there exists `f ∈ R` with `f ∉ p` such that localization away from `f` is a free
`R_f`-module. -/
@[stacks 0GWM "prime-complement specialization of the localization owner"]
#check @Module.FinitePresentation.exists_free_localizedModule_powers

@[stacks 0GWM "canonical localized-module map"]
#check @LocalizedModule.mkLinearMap
