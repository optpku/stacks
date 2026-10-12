/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Smooth.Adic.ClosedFiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Complete Local Formally Smooth Lifts

@stack 07NR
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v

/-- Lemma 15.40.6 (07NR): an adically formally smooth complete local algebra over the residue
field of a Noetherian complete local ring lifts to an adically formally smooth complete local
algebra over that ring, with the prescribed closed fiber. -/
@[stacks 07NR "complete local formally smooth lift with prescribed closed fiber"]
theorem exists_completeLocal_formallySmooth_lift_with_closedFiber
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsCompleteLocalRing A]
    [IsNoetherianRing B] [IsCompleteLocalRing B]
    [Algebra (ResidueField A) B]
    (hfs : (algebraMap (ResidueField A) B).formally_smooth_for_adic (maximalIdeal B)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : IsNoetherianRing C)
      (_ : IsCompleteLocalRing C) (_ : IsLocalHom (algebraMap A C))
      (_ : Ideal.Fiber (maximalIdeal A) C ≃ₐ[ResidueField A] B),
      (algebraMap A C).formally_smooth_for_adic (maximalIdeal C) := sorry
