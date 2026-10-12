/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Tate.PseudoCoherent
import StacksCheckRecall

@[expose] public section

universe u w

section FinitePresentation

variable {R : Type u} {S : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [(algebraMap R S).IsPseudoCoherentRingMap]

/- Lemma 23.6.10 (Tag 0BZ9): a pseudo-coherent ring map admits a finite polynomial presentation
and a Tate resolution with finitely many generators in every degree, without any additional
Noetherian hypothesis. -/
@[stacks 0BZ9]
#check (TateResolution.exists_finitePresentation_of_isPseudoCoherent (R := R) (S := S) :
  ∃ (n : ℕ) (pi0 : MvPolynomial (Fin n) R →ₐ[R] S),
    Function.Surjective pi0 ∧
      ∃ A : TateResolution.{u, 0, w} pi0, A.HasFinitePositiveGenerators)

end FinitePresentation

#check @TateResolution.exists_finite_of_isPseudoCoherent
#check @TateResolution.HasFinitePositiveGenerators
