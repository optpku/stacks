/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.RingTheory.RingHom.Perfect.Regular
import StacksCheckRecall

/-!
# Lemma 15.83.5

@stack 067K
-/

@[expose] public section

universe u v

/-!
# Lemma 15.83.5 compatibility entry point

The regular finite-dimensional base criterion for perfect ring maps is owned
by `ReasLib.RingTheory.RingHom.Perfect.Regular`.
-/

/- Lemma 15.83.5, tag `067K`: finite type maps out of finite-dimensional regular rings are
perfect. -/
@[stacks 067K "finite type over a finite-dimensional regular ring"]
#check fun (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsRegularRing A] [Algebra.FiniteType A B] (h_finite : ∃ d : ℕ, Ring.KrullDimLE d A) =>
  (Algebra.isPerfectRingMap_of_finiteType_of_isRegularRing_of_finiteDimension
    A B h_finite : (algebraMap A B).IsPerfectRingMap)
