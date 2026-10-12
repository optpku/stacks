/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.Factorization

@[expose] public section

universe u v w

namespace TameSymbol.Factorization

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing B] [Algebra A B] [Module.Finite A B]
variable [CommRing C] [Algebra A C] [Module.Finite A C]
variable {a₁ a₂ : A}

/-- The residue-field unit computed from a finite extension and chosen local factorizations is
independent of all these choices. -/
theorem value_eq (D : Factorization A B a₁ a₂) (E : Factorization A C a₁ a₂) :
    D.value = E.value := sorry

end TameSymbol.Factorization
