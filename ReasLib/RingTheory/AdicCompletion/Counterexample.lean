/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

universe u

namespace AdicCompletion

/-- There exist a commutative ring `A`, a principal ideal `I` for which `A` is
`I`-adically complete, and an element `f : A` such that the `I`-adic
completion of `Localization.Away f` is not flat over `A`. -/
theorem exists_principal_away_notFlat :
    ∃ (A : Type u) (_ : CommRing A) (I : Ideal A) (f : A),
      I.IsPrincipal ∧ IsAdicComplete I A ∧
        ¬ Module.Flat A (AdicCompletion I (Localization.Away f)) := sorry

end AdicCompletion

namespace IsAdicComplete

/-- There exist a commutative ring `R` and principal ideals `I` and `J` such
that `R` is `I`-adically complete while `R ⧸ J` is not `I`-adically complete. -/
theorem exists_principal_quotient_not_adicComplete :
    ∃ (R : Type u) (_ : CommRing R) (I J : Ideal R),
      I.IsPrincipal ∧ IsAdicComplete I R ∧ J.IsPrincipal ∧
        ¬ IsAdicComplete I (R ⧸ J) := sorry

end IsAdicComplete
