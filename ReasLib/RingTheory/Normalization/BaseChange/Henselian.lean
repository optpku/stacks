/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import ReasLib.RingTheory.Henselian.Flat
public import ReasLib.RingTheory.Normalization.BaseChange.Flat

@[expose] public section

/-!
# Henselian and complete base changes of normalization

This leaf specializes the flat normalization base-change maps to henselizations, strict
henselizations, and maximal-ideal completions.  The underlying flat construction remains in
`Normalization.BaseChange.Flat`.
-/

open IsLocalRing
open scoped TensorProduct nonZeroDivisors

universe u v

namespace Normalization.BaseChange

namespace Henselization

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type v} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

/-- The normalization tensor base change maps to the total quotient ring of a henselization. -/
noncomputable def tensorToTotalQuotient :
    Normalization.normalizationRing R ⊗[R] Rh →ₐ[R] Localization.totalQuotientRing Rh :=
  -- Local instance justification (search instability): select henselization flatness for this map.
  letI : Module.Flat R Rh := IsHenselizationOf.moduleFlat
  BaseChange.tensorToTotalQuotient

/-- The algebra structure on the total quotient ring of a henselization induced by the
normalization tensor map. -/
noncomputable abbrev algebra :
    Algebra (Normalization.normalizationRing R ⊗[R] Rh) (Localization.totalQuotientRing Rh) :=
  RingHom.toAlgebra (tensorToTotalQuotient (R := R) (Rh := Rh)).toRingHom

end

end Henselization

namespace StrictHenselization

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rsh : Type v} [CommRing Rsh] [Algebra R Rsh]

/-- The normalization tensor base change maps to the total quotient ring of an ind-etale strict
henselization candidate. -/
noncomputable def tensorToTotalQuotient
    (hcolim : RingHom.IndEtale.Raw (algebraMap R Rsh)) :
    Normalization.normalizationRing R ⊗[R] Rsh →ₐ[R] Localization.totalQuotientRing Rsh :=
  -- Local instance justification (search instability): use flatness from this ind-etale presentation.
  letI : Module.Flat R Rsh := moduleFlat_of_indEtale hcolim
  BaseChange.tensorToTotalQuotient

/-- The algebra structure induced by the strict-henselization normalization tensor map. -/
noncomputable abbrev algebra
    (hcolim : RingHom.IndEtale.Raw (algebraMap R Rsh)) :
    Algebra (Normalization.normalizationRing R ⊗[R] Rsh) (Localization.totalQuotientRing Rsh) :=
  RingHom.toAlgebra (tensorToTotalQuotient hcolim).toRingHom

end

end StrictHenselization

namespace Completion

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The normalization tensor base change maps to the total quotient ring of the maximal-ideal
completion. -/
noncomputable def tensorToTotalQuotient :
    Normalization.normalizationRing R ⊗[R] AdicCompletion (maximalIdeal R) R →ₐ[R]
      Localization.totalQuotientRing (AdicCompletion (maximalIdeal R) R) :=
  BaseChange.tensorToTotalQuotient

/-- The algebra structure induced by the completion normalization tensor map. -/
noncomputable abbrev algebra :
    Algebra (Normalization.normalizationRing R ⊗[R] AdicCompletion (maximalIdeal R) R)
      (Localization.totalQuotientRing (AdicCompletion (maximalIdeal R) R)) :=
  RingHom.toAlgebra (tensorToTotalQuotient (R := R)).toRingHom

end

end Completion

end Normalization.BaseChange
