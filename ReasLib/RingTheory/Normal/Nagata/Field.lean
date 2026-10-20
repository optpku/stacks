module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Nagata Fields

This leaf provides the canonical Nagata-ring instance for fields.
-/

universe u

namespace NagataRing

/-- Fields are Nagata rings. -/
@[stacks 0335 "field case"]
instance instOfField (K : Type u) [Field K] : NagataRing K where
  quotient_isN2Ring := by
    intro p hp
    -- Local instance justification (proof-local temporary data): the quantified ideal's primality witness is used only inside this proof.
    letI : p.IsPrime := hp
    -- Local instance justification (proof-local temporary data): maximality is derived from primality because the coefficient ring is a field.
    letI : p.IsMaximal := by
      rw [p.eq_bot_of_prime]
      exact Ideal.bot_isMaximal
    -- Local instance justification (proof-local temporary data): the quotient field is needed solely to discharge the quotient-ring instance goal here.
    letI : Field (K ⧸ p) := Ideal.Quotient.field p
    infer_instance

end NagataRing
