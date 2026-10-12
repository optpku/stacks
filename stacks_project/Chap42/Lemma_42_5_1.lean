/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.Factorization.Independence
import StacksCheckRecall

@[expose] public section

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing B] [Algebra A B] [Module.Finite A B]
variable [CommRing C] [Algebra A C] [Module.Finite A C]
variable {a₁ a₂ : A}

/- Lemma 42.5.1: the residue-field unit computed from a finite extension and chosen local
factorizations is independent of all these choices. -/
@[stacks 0EAR] #check (TameSymbol.Factorization.value_eq :
  ∀ (D : TameSymbol.Factorization A B a₁ a₂)
      (E : TameSymbol.Factorization A C a₁ a₂), D.value = E.value)
