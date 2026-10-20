/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Prime fibers of ring maps

Small set-level consequences of Mathlib's `Ideal.primesOver` owner. These
lemmas keep finite-fiber arguments from reconstructing the same subtype-to-set
conversion in chapter-local proofs.
-/

universe u v w

namespace Ideal

/-- A nonempty subsingleton fiber of prime ideals is the singleton given by its
distinguished prime. -/
@[stacks 00UK "singleton prime fiber"]
theorem primesOver_eq_singleton
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (r : p.primesOver A)
    [Subsingleton (p.primesOver A)] :
    p.primesOver A = ({r.1} : Set (Ideal A)) := sorry

/-- A singleton prime fiber descends to every integral intermediate algebra in a scalar tower. -/
@[stacks 00UK "singleton prime fiber descends through an integral tower"]
theorem primesOver_eq_singleton_under_of_tower
    {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.IsIntegral S T] [FaithfulSMul S T]
    (p : Ideal R) (Q : Ideal T) (hQ : p.primesOver T = {Q}) :
    p.primesOver S = {Q.under S} := sorry

end Ideal
