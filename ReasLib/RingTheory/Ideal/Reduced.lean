module

public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reduced ideals

Small ideal-side consequences of reducedness that are independent of spectrum constructions.
-/

@[expose] public section

universe u

namespace Ideal

/-- In a reduced commutative ring, the radical of the zero ideal is zero. -/
@[stacks 00EW "radical of zero in a reduced ring"]
theorem radical_bot_of_isReduced {R : Type u} [CommRing R] [IsReduced R] :
    (⊥ : Ideal R).radical = ⊥ :=
  (Ideal.radical_eq_iff).2 Ideal.isRadical_bot

end Ideal
