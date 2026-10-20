module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.MvPolynomial.Noetherian
public import ReasLib.RingTheory.Normal.Nagata

/-!
# Japanese polynomial rings in countably many variables

Polynomial rings in countably many variables over a field or over `ℤ` are N-2, despite not
being Noetherian.  The non-Noetherian half is already covered by the generic infinite-variable
criterion in `ReasLib.RingTheory.MvPolynomial.Noetherian`; this leaf owns only the two N-2
statements.

@stack 0350
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- Example 10.161.2: the polynomial ring in countably many variables over a field is N-2. -/
@[stacks 0350 "field coefficients"]
theorem isN2Ring_pnat_of_field (k : Type u) [Field k] :
    IsN2Ring (MvPolynomial ℕ+ k) := sorry

/-- Example 10.161.2: the polynomial ring in countably many variables over `ℤ` is N-2. -/
@[stacks 0350 "integer coefficients"]
theorem isN2Ring_pnat_int : IsN2Ring (MvPolynomial ℕ+ ℤ) := sorry

end MvPolynomial
