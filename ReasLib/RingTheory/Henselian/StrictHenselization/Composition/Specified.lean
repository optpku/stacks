/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselization.Composition
public import ReasLib.RingTheory.Henselian.StrictHenselization.Specified

@[expose] public section

/-!
# Specified Strict Henselizations over a Henselization

@stack 0BSL

The neutral composition theorem is independent of residue-field coordinates.
This leaf records the source-facing existence statement after a henselization
and a separable closure of the original residue field have both been fixed.
-/

open IsLocalRing

universe u

namespace IsStrictHenselizationOf

/-- Remark 10.155.4 (0BSL): for a fixed henselization `Rh` of `R` and a fixed separable closure
of `ResidueField R`, there is a strict henselization of `Rh` whose residue-field coordinate is
compatible with the original residue-field map. -/
@[stacks 0BSL "specified strict henselization over a henselization"]
theorem exists_over_henselization_with_residueFieldEquiv
    {R Rh Ksep : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    [Field Ksep] [Algebra (ResidueField R) Ksep]
    [IsSepClosure (ResidueField R) Ksep] :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra Rh Rsh)
      (_ : IsStrictHenselizationOf Rh Rsh) (ι : ResidueField Rsh ≃+* Ksep),
      ι.toRingHom.comp
          (ResidueField.map ((algebraMap Rh Rsh).comp (algebraMap R Rh))) =
        algebraMap (ResidueField R) Ksep := sorry

end IsStrictHenselizationOf
