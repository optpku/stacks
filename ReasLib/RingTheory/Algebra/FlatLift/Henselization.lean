/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Pair.BaseChange
public import ReasLib.RingTheory.Algebra.FlatLift.Basic
public import ReasLib.RingTheory.RingHom.Syntomic.Complement
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Flat algebra lifts versus pair henselization
-/

@[expose] public section

universe u

noncomputable section

open RingPairCat

namespace Algebra.NilpotentLift

/-- For a surjection of Noetherian rings with nilpotent kernel, a finite-type
flat algebra, and an ideal on whose complement the algebra map is syntomic, a
flat lift exists if and only if the pair henselization admits a flat lift. -/
theorem existsFlatLift_iff_existsFlatLift_henselization
    {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] [IsNoetherianRing A'] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Flat A B]
    [henselianPairInclusion.IsRightAdjoint]
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (b : Ideal B) (hsyn : (algebraMap A B).SyntomicOnComplement b) :
    existsFlatLift A' A B ↔
      existsFlatLift A' A (henselizationRing (pairOfIdeal b)) :=
  sorry

end Algebra.NilpotentLift

end
