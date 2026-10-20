/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.RingTheory.RingHom.Perfect.Flat
import StacksCheckRecall

/-!
# Lemma 15.83.4

@stack 067J
-/

@[expose] public section

universe u v

/-!
# Lemma 15.83.4 compatibility entry point

The canonical perfectness instance for flat finitely presented ring maps is
owned by `ReasLib.RingTheory.RingHom.Perfect.Flat`.
-/

/- Lemma 15.83.4, tag `067J`: flat finitely presented maps are perfect. -/
@[stacks 067J "flat finitely presented map"]
#check fun (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] =>
  (Algebra.instIsPerfectRingMapOfFlatOfFinitePresentation A B :
    (algebraMap A B).IsPerfectRingMap)
