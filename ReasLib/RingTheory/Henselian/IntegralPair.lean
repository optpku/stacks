/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integral extensions of henselian pairs

Henselianity of a pair is preserved when its ideal is extended along an integral algebra map.
The mapped ideal keeps the source algebra and ideal visible in the class head, so this transfer is
available as a named instance without introducing a separate pair predicate.

@stack 09XK
-/

@[expose] public section

universe u v

/-- Lemma 15.11.8 (09XK): if `(A, I)` is a henselian pair and `A → B` is integral, then
`(B, Ideal.map (algebraMap A B) I)` is a henselian pair. -/
@[stacks 09XK "integral extensions of henselian pairs"]
instance ideal_map_henselianRing_of_isIntegral
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [HenselianRing A I] [Algebra.IsIntegral A B] :
    HenselianRing B (Ideal.map (algebraMap A B) I) := sorry
-- Proof strategy: use the Gabber root/idempotent-lifting criterion for both pairs, descend a
-- finite target configuration to a finite integral `A`-subalgebra, apply henselianity of
-- `(A, I)`, and transport bijectivity through the quotient and scalar-extension maps.
