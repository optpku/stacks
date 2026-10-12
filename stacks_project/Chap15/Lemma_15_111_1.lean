/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Invariant.FixedPoints

/-!
@stack 0BRF
-/

@[expose] public section

universe u v w

open Polynomial

/- Lemma 15.111.1 (current Stacks numbering: Lemma 15.112.1, tag `0BRF`):
if a finite group acts on a surjective equivariant map A ⟶ B, every fixed
element of B has a monic orbit polynomial over the fixed subring of A. -/
@[stacks 0BRF "Lemma 15.111.1"]
#check fun (G : Type u) [Group G] (A : Type v) (B : Type w)
    [CommRing A] [CommRing B] [MulSemiringAction G A] [MulSemiringAction G B]
    [Finite G] (φ : A →+*[G] B) (hφ : Function.Surjective φ)
    (b : FixedPoints.subring B G) ↦
  (MulSemiringActionHom.exists_monic_map_eq_orbit φ hφ b :
    ∃ P : Polynomial (FixedPoints.subring A G), P.Monic ∧
      P.map φ.fixedPoints = (X - C b) ^ Nat.card G)
