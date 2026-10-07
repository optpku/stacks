module

public import Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsSepClosed
public import ReasLib.FieldTheory.IsSepClosed.Equiv

@[expose] public section

/-!
# Strict Henselian Local Rings

A local ring is strictly henselian if it is henselian and its residue field is separably
algebraically closed.

## Main definitions

* `StrictHenselianLocalRing` — henselian local ring with separably closed residue field.

## Main results

* Separably closed fields are strictly henselian.
-/

open IsLocalRing

universe u

section

variable (R : Type u) [CommRing R]

/-- A local ring is strictly henselian if it is henselian and its residue field is separably
algebraically closed. -/
@[stacks 04GK]
class StrictHenselianLocalRing : Prop extends HenselianLocalRing R, IsSepClosed (ResidueField R)

/-- Strict henselianity supplies both henselianity and a separably closed residue field. -/
@[stacks 04GK "strict henselian conditions"]
theorem StrictHenselianLocalRing.spec [StrictHenselianLocalRing R] :
    HenselianLocalRing R ∧ IsSepClosed (ResidueField R) := sorry

variable (K : Type u) [Field K] [IsSepClosed K]

/-- A separably closed field is strictly henselian. -/
instance instStrictHenselianLocalRing : StrictHenselianLocalRing K := sorry

end
