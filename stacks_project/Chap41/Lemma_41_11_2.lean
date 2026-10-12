/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Locus
import StacksCheckRecall

universe u v

/- Lemma 41.11.2: for a finite-type algebra over a Noetherian ring, étaleness
at a prime `q` lying over `p` is equivalent to essential étaleness of the
canonical local homomorphism `Aₚ → B_q`. -/
@[stacks 039L] #check
  (Algebra.IsEtaleAt.iff_localRingHom_of_liesOver :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsNoetherianRing A] [Algebra.FiniteType A B]
      (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p],
      Algebra.IsEtaleAt A q ↔
        (Localization.localRingHom p q (algebraMap A B) (q.over_def p)).EssEtale)
