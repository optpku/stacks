/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Finiteness.Projective
public import ReasLib.RingTheory.Ideal.QuasiRegular

/-!
# Cotangent Modules of Quasi-Regular Ideals

@stack 08RK

This leaf owns the finite-projectivity consequence of quasi-regularity for
the canonical conormal module `I.Cotangent`.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R] {I : Ideal R}

namespace IsQuasiRegularIdeal

/-- Lemma 15.32.3 (Stacks tag `08RK`): the cotangent module `I / I²` of a
quasi-regular ideal is finite projective over `R ⧸ I`. -/
@[stacks 08RK "quasi-regular ideal cotangent module"]
theorem cotangent_finiteProjective
    (hI : I.IsQuasiRegularIdeal) :
    Module.FiniteProjective (R ⧸ I) I.Cotangent := sorry

end IsQuasiRegularIdeal

end Ideal
