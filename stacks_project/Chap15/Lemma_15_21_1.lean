/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Polynomial.LinearFactor
import StacksCheckRecall

/-!
# Lemma 15.21.1

@stack 052Z
-/

@[expose] public section

open Polynomial

universe u

@[stacks 052Z]
#check fun {R : Type u} [CommRing R] (P : R[X]) (hP : P.Monic) {a : R}
    (ha : P.IsRoot a) ↦
  (Polynomial.Monic.exists_eq_X_sub_C_mul_of_isRoot hP ha :
    ∃ Q : R[X], Q.Monic ∧ P = (X - C a) * Q)

#check @Polynomial.mul_divByMonic_eq_iff_isRoot
#check @Polynomial.Monic.of_mul_monic_left
