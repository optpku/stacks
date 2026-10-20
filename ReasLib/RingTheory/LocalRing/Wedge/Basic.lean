/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Wedge.Compatibility

/-!
# Finite Wedges of Local Rings

This module defines finite wedges of local rings using tuples with compatible residues.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace LocalRing.Wedge

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {m : ℕ}
variable (As : Fin (m + 1) → Type v)
variable [∀ i, CommRing (As i)] [∀ i, IsLocalRing (As i)]

/-- The subring of a finite product whose coordinates have compatible residues. -/
noncomputable def subring
    (residueFieldEquivToLast :
      ∀ i : Fin m,
        IsLocalRing.ResidueField (As i.castSucc) ≃+*
          IsLocalRing.ResidueField (As (Fin.last m))) :
    Subring (∀ i : Fin (m + 1), As i) :=
  RingHom.eqLocus
    (RingHom.pi fun i : Fin m ↦
      (residueFieldEquivToLast i).toRingHom.comp
        ((residue (As i.castSucc)).comp (Pi.evalRingHom As i.castSucc)))
    (RingHom.pi fun _ : Fin m ↦
      (residue (As (Fin.last m))).comp (Pi.evalRingHom As (Fin.last m)))

/-- Membership in `subring` is exactly compatibility of the coordinate residues. -/
theorem mem_subring_iff
    (residueFieldEquivToLast :
      ∀ i : Fin m,
        IsLocalRing.ResidueField (As i.castSucc) ≃+*
          IsLocalRing.ResidueField (As (Fin.last m)))
    (a : ∀ i : Fin (m + 1), As i) :
    a ∈ subring As residueFieldEquivToLast ↔
      compatible As residueFieldEquivToLast a := sorry

/-- A local ring is a wedge of a finite family when it is isomorphic to the subring of tuples
with compatible residues for some identifications of the residue fields. -/
def IsWedgeOf
    (A : Type u) [CommRing A] [IsLocalRing A]
    (As : Fin (m + 1) → Type v) [∀ i, CommRing (As i)] [∀ i, IsLocalRing (As i)] : Prop :=
  ∃ residueFieldEquivToLast :
      ∀ i : Fin m,
        IsLocalRing.ResidueField (As i.castSucc) ≃+*
          IsLocalRing.ResidueField (As (Fin.last m)),
    Nonempty (A ≃+* subring As residueFieldEquivToLast)

/-- A local ring is a wedge precisely when suitable residue-field identifications and a ring
equivalence with the compatible-residue subring exist. -/
theorem isWedgeOf_iff :
    IsWedgeOf A As ↔
      ∃ residueFieldEquivToLast :
          ∀ i : Fin m,
            IsLocalRing.ResidueField (As i.castSucc) ≃+*
              IsLocalRing.ResidueField (As (Fin.last m)),
        Nonempty (A ≃+* subring As residueFieldEquivToLast) := sorry

/-- A wedge condition yields residue-field identifications and a ring equivalence
with the compatible-residue subring. -/
theorem IsWedgeOf.spec
    (h : IsWedgeOf A As) :
    ∃ residueFieldEquivToLast :
        ∀ i : Fin m,
          IsLocalRing.ResidueField (As i.castSucc) ≃+*
            IsLocalRing.ResidueField (As (Fin.last m)),
      Nonempty (A ≃+* subring As residueFieldEquivToLast) := sorry

end

end LocalRing.Wedge
