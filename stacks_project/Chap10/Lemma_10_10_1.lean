/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Exact.Hom
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.10.1

@stack 0582

Lemma 10.10.1 is owned by the neutral linear-map exactness leaf.  The chapter
keeps only the two source clauses as tagged canonical recalls.
-/

/- Lemma 10.10.1 (1): `M₁ → M₂ → M₃ → 0` is exact if and only if every
contravariant Hom sequence is exact. -/
@[stacks 0582 "(1), contravariant Hom criterion"]
#check @LinearMap.exact_surjective_iff_forall_lcomp

/- Lemma 10.10.1 (2): `0 → M₁ → M₂ → M₃` is exact if and only if every
covariant Hom sequence is exact. -/
@[stacks 0582 "(2), covariant Hom criterion"]
#check @LinearMap.injective_exact_iff_forall_compRight
