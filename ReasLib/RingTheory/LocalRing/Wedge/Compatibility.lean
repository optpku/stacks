module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances

@[expose] public section

/-!
# Compatibility of Residues in Finite Local-Ring Families

This module provides the proposition-level compatibility condition underlying finite wedges
of local rings.
-/

open IsLocalRing

universe u v

namespace LocalRing.Wedge

section

variable {m : ℕ}
variable (As : Fin (m + 1) → Type v)
variable [∀ i, CommRing (As i)] [∀ i, IsLocalRing (As i)]

/-- A tuple is compatible when all earlier residues agree with the last residue after the
specified residue-field identifications. -/
def compatible
    (residueFieldEquivToLast :
      ∀ i : Fin m,
        IsLocalRing.ResidueField (As i.castSucc) ≃+*
          IsLocalRing.ResidueField (As (Fin.last m)))
    (a : ∀ i : Fin (m + 1), As i) : Prop :=
  ∀ i : Fin m,
    residueFieldEquivToLast i (residue (As i.castSucc) (a i.castSucc)) =
      residue (As (Fin.last m)) (a (Fin.last m))

/-- Unfold residue compatibility into equality of all earlier residues with the last residue. -/
@[simp]
theorem compatible_iff
    (residueFieldEquivToLast :
      ∀ i : Fin m,
        IsLocalRing.ResidueField (As i.castSucc) ≃+*
          IsLocalRing.ResidueField (As (Fin.last m)))
    (a : ∀ i : Fin (m + 1), As i) :
    compatible As residueFieldEquivToLast a ↔
      ∀ i : Fin m,
        residueFieldEquivToLast i (residue (As i.castSucc) (a i.castSucc)) =
          residue (As (Fin.last m)) (a (Fin.last m)) := sorry

end

end LocalRing.Wedge
