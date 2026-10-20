/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Module.ContentIdeal

/-!
# Definition 15.24.1

The source definition is recalled from the generic content-ideal owner; the
flatness assumption remains visible in the tagged source view.

@stack 0ASA
-/

@[expose] public section

universe u v

/- Definition 15.24.1: for a flat module, `I` is the content ideal of `x`
when it is the least ideal whose multiple of the module contains `x`. -/
@[stacks 0ASA "Definition 15.24.1"]
#check fun (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M]
    [Module A M] [Module.Flat A M] (x : M) (I : Ideal A) ↦
  IsContentIdeal x I

/- The reusable predicate is meaningful for arbitrary modules over a
commutative semiring. -/
#check @IsContentIdeal
#check @IsContentIdeal.iff
#check @IsContentIdeal.mem
#check @IsContentIdeal.le
#check @IsContentIdeal.unique
