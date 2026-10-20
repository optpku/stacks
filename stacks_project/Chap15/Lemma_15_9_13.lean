/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.SymmetricAlgebra.Smooth
import StacksCheckRecall

/-!
# Lemma 15.9.13

@stack 07M6
-/

@[expose] public section

universe u v

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommMonoid M] [Module A M]

/- Lemma 15.9.13: `SymmetricAlgebra A M` is smooth over `A` if and only if `M` is a finite
projective `A`-module. -/
@[stacks 07M6]
#check
  (SymmetricAlgebra.smooth_iff_finiteProjective (A := A) (M := M) :
    Algebra.Smooth A (SymmetricAlgebra A M) ↔ Module.FiniteProjective A M)
