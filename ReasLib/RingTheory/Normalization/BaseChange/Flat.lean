/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.RingTheory.Localization.TotalQuotient.Algebra
public import ReasLib.RingTheory.Normalization.Basic

@[expose] public section

/-!
# Flat base change of normalization

This leaf owns the canonical maps from a normalization and its tensor base change into the total
quotient ring of a flat algebra.  It does not assume that the target algebra is henselian or
complete; those specializations live in the neighboring `Henselian` and `Completion` leaves.
-/

universe u v

open scoped TensorProduct nonZeroDivisors

namespace Normalization.BaseChange

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- The normalization of `R` maps canonically to the total quotient ring of a flat `R`-algebra
`S`. -/
noncomputable def toTotalQuotient :
    Normalization.normalizationRing R →ₐ[R] Localization.totalQuotientRing S :=
  (IsScalarTower.toAlgHom R (integralClosure R (Localization.totalQuotientRing S))
      (Localization.totalQuotientRing S)).comp
    ((Localization.totalQuotientAlgMap :
        Localization.totalQuotientRing R →ₐ[R] Localization.totalQuotientRing S).mapIntegralClosure)

/-- Compute the flat normalization map on an element of the source normalization. -/
theorem toTotalQuotient_apply (x : Normalization.normalizationRing R) :
    toTotalQuotient x =
      (IsScalarTower.toAlgHom R (integralClosure R (Localization.totalQuotientRing S))
        (Localization.totalQuotientRing S))
        (((Localization.totalQuotientAlgMap :
          Localization.totalQuotientRing R →ₐ[R] Localization.totalQuotientRing S).mapIntegralClosure) x) := sorry

/-- The canonical tensor/base-change map from `normalizationRing R ⊗[R] S` to the total quotient
ring of `S`. -/
noncomputable def tensorToTotalQuotient :
    Normalization.normalizationRing R ⊗[R] S →ₐ[R] Localization.totalQuotientRing S :=
  Algebra.TensorProduct.productMap
    (toTotalQuotient :
      Normalization.normalizationRing R →ₐ[R] Localization.totalQuotientRing S)
    (IsScalarTower.toAlgHom R S (Localization.totalQuotientRing S))

/-- Compute the tensor normalization map on a pure tensor. -/
theorem tensorToTotalQuotient_tmul
    (x : Normalization.normalizationRing R) (s : S) :
    tensorToTotalQuotient (TensorProduct.tmul R x s) =
      toTotalQuotient x * algebraMap S (Localization.totalQuotientRing S) s := sorry

end

end Normalization.BaseChange
