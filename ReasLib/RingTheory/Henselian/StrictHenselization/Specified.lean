/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.SeparableClosure
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization.ResidueCoordinate
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict henselizations with a specified residue field

This module records existence of a strict henselization together with a
specified separable closure of the residue field and compatible henselization
data.
-/

@[expose] public section

open IsLocalRing

universe u

namespace IsStrictHenselizationOf

/-- A chosen separable closure of the residue field is realized by a strict
henselization, compatibly with a henselization of the base. -/
@[stacks 04GP "strict henselization with specified residue field"]
theorem exists_with_henselization_and_residueFieldEquiv
    (R : Type u) [CommRing R] [IsLocalRing R]
    (Ksep : Type u) [Field Ksep] [Algebra (ResidueField R) Ksep]
    [IsSepClosure (ResidueField R) Ksep] :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh) (_ : IsHenselizationOf R Rh)
      (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh)
      (_ : IsStrictHenselizationOf R Rsh) (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh)
      (_ : IsLocalHom (algebraMap Rh Rsh)) (φ : ResidueField Rsh ≃+* Ksep),
      φ.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) Ksep := sorry

end IsStrictHenselizationOf
