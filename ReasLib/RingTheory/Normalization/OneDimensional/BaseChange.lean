module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normalization.BaseChange.Henselian
public import ReasLib.RingTheory.Normalization.OneDimensional.Completion
public import ReasLib.RingTheory.Normalization.OneDimensional.Henselization

/-!
# Normalization base change in dimension one

This leaf identifies the normalization tensor base change with the integral
closure after henselization, strict henselization, or maximal-ideal completion.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

noncomputable section

universe u v

namespace Normalization.OneDimensional

namespace Henselization

variable {A : Type u} {Ah : Type v}
variable [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-- After henselization, the normalization tensor base change is the integral closure in the
total quotient ring. -/
@[stacks 0C3V]
theorem isIntegralClosure (h_dimension : ringKrullDim A = 1) :
    let _ : Algebra (normalizationRing A ⊗[A] Ah) (Localization.totalQuotientRing Ah) :=
      Normalization.BaseChange.Henselization.algebra
    IsIntegralClosure (normalizationRing A ⊗[A] Ah) Ah
      (Localization.totalQuotientRing Ah) := sorry

end Henselization

namespace StrictHenselization

variable {A : Type u} {Ash : Type v}
variable [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-- After strict henselization, the normalization tensor base change is the integral closure in
the total quotient ring. -/
@[stacks 0C3V]
theorem isIntegralClosure (h_dimension : ringKrullDim A = 1) :
    let _ : Algebra (normalizationRing A ⊗[A] Ash) (Localization.totalQuotientRing Ash) :=
      Normalization.BaseChange.StrictHenselization.algebra
        (IsStrictHenselizationOf.rawIndEtale (R := A) (S := Ash))
    IsIntegralClosure (normalizationRing A ⊗[A] Ash) Ash
      (Localization.totalQuotientRing Ash) := sorry

end StrictHenselization

namespace Completion

variable {A : Type u} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]

/-- After maximal-ideal completion, the normalization tensor base change is the integral closure
in the total quotient ring. -/
@[stacks 0C3V]
theorem isIntegralClosure (h_dimension : ringKrullDim A = 1) :
    let _ : Algebra
        (normalizationRing A ⊗[A] AdicCompletion (maximalIdeal A) A)
        (Localization.totalQuotientRing (AdicCompletion (maximalIdeal A) A)) :=
      Normalization.BaseChange.Completion.algebra
    IsIntegralClosure
      (normalizationRing A ⊗[A] AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal A) A)
      (Localization.totalQuotientRing (AdicCompletion (maximalIdeal A) A)) := sorry

end Completion

end Normalization.OneDimensional
