/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.DirectLimit
import StacksCheckRecall

/-!
# Lemma 15.11.13

@stack 0FWT
-/

@[expose] public section

universe u v

variable {J : Type v} [Preorder J] [Nonempty J] [IsDirectedOrder J]
variable (A : J → Type u) [∀ j, CommRing (A j)]
variable (I : ∀ j, Ideal (A j))
variable (f : ∀ j k, j ≤ k → A j →+* A k)
variable [DirectedSystem A (f · · ·)]
variable (hI : ∀ ⦃j k⦄ (h : j ≤ k), Ideal.map (f j k h) (I j) ≤ I k)
variable [∀ j, HenselianRing (A j) (I j)]

-- Lemma 15.11.13 (0FWT): the colimit pair of a compatible directed system of henselian
-- pairs is henselian.
@[stacks 0FWT]
#check
  (Ring.DirectLimit.directedSystem_directLimit_henselianRing
      (A := A) (I := I) (f := f) hI :
    HenselianRing (Ring.DirectLimit A (f · · ·))
      (⨆ j, Ideal.map (Ring.DirectLimit.of A (f · · ·) j) (I j)))
