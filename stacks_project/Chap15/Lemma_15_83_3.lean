/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Noetherian
import StacksCheckRecall

/-!
# Lemma 15.83.3

@stack 067I
-/

@[expose] public section

universe u v

/-!
# Lemma 15.83.3 compatibility entry point

The Noetherian finite-type criterion for pseudo-coherent ring maps is owned
by `ReasLib.RingTheory.RingHom.PseudoCoherent.Noetherian`.
-/

/- Lemma 15.83.3, tag `067I`: finite type maps out of Noetherian rings are
pseudo-coherent. -/
@[stacks 067I "finite type over a Noetherian ring"]
#check fun (R : Type u) (A : Type v) [CommRing R] [IsNoetherianRing R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A] =>
  (Algebra.isPseudoCoherentRingMap_of_finiteType_of_isNoetherianRing (R := R) (A := A) :
    (algebraMap R A).IsPseudoCoherentRingMap)
