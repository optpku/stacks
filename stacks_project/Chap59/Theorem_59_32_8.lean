/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselization.Specified
import StacksCheckRecall

@[expose] public section

universe u

/- Theorem 59.32.8: canonical henselization and strict henselization maps of a
local ring, with the chosen separable closure realized as the strict residue
field. -/
@[stacks 03QL]
#check (IsStrictHenselizationOf.exists_with_henselization_and_residueFieldEquiv :
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (Ksep : Type u) [Field Ksep] [Algebra (IsLocalRing.ResidueField R) Ksep]
    [IsSepClosure (IsLocalRing.ResidueField R) Ksep],
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh) (_ : IsHenselizationOf R Rh)
      (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra R Rsh)
      (_ : IsStrictHenselizationOf R Rsh) (_ : Algebra Rh Rsh) (_ : IsScalarTower R Rh Rsh)
      (_ : IsLocalHom (algebraMap Rh Rsh))
      (φ : IsLocalRing.ResidueField Rsh ≃+* Ksep),
      φ.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap R Rsh)) =
        algebraMap (IsLocalRing.ResidueField R) Ksep)

-- Declarations for this item will be appended below by the statement pipeline.
