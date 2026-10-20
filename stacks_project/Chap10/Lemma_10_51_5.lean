/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.KrullIntersection.Localization
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-!
# Krull intersection localization

Lemma 10.51.5 retains its principal-open conclusion as a source-facing bridge
to the reusable prime-local API.  Its Jacobson-radical clause is a direct
canonical Mathlib recall.
@stack 00IQ
-/

@[stacks 00IQ "(1), prime-local companion"]
#check @Ideal.iInf_pow_smul_localized_eq_bot_of_le

/- Lemma 10.51.5 (1): the principal-open vanishing statement is owned directly by ReasLib. -/
@[stacks 00IQ "(1), principal-open vanishing"]
#check @Ideal.exists_notMem_iInf_pow_smul_localized_eq_bot

/- Lemma 10.51.5 (2): if `I` is contained in the Jacobson radical of `R`, then the `I`-adic
intersection `⋂ n, I^n M` is zero. This is exactly the canonical mathlib theorem
`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`; the Jacobson radical of the ring is expressed
canonically as `(⊥ : Ideal R).jacobson`. -/
@[stacks 00IQ "(2), Jacobson-radical vanishing"]
#check @Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
