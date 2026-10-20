/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Smooth.Adic.Lifting
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Extending derivations across adically formally smooth maps

Adic formal smoothness lifts the dual-number map associated to a derivation.  Taking the
square-zero component of that lift extends the derivation to the complete target.

@stack 07PL
-/

@[expose] public section

universe u v

namespace RingHom

/-- An adically formally smooth map into an adically complete target extends every absolute
derivation of the source to an absolute derivation of the target. -/
@[stacks 07PL "adic derivation extension"]
theorem exists_derivationExtension
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal B) [IsAdicComplete I B]
    (hfs : f.formally_smooth_for_adic I) (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ a : A, D' (f a) = f (D a) := sorry

/-- Lemma 15.49.1 (Stacks `07PL`): a formally smooth local map of Noetherian local rings into a
complete target extends every absolute derivation of the source. -/
@[stacks 07PL "complete-local derivation extension"]
theorem exists_derivationExtension_of_completeLocal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing A] [IsCompleteLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hfs : (algebraMap A B).formally_smooth_for_adic (IsLocalRing.maximalIdeal B))
    (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B,
      ∀ a : A, D' (algebraMap A B a) = algebraMap A B (D a) := sorry

end RingHom
