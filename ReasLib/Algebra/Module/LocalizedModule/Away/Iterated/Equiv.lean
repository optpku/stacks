/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Iterated
public import ReasLib.Algebra.Module.LocalizedModule.Equiv
public import ReasLib.Algebra.Module.LocalizedModule.Iterated
public import ReasLib.Algebra.Module.LocalizedModule.Units
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical Product Comparison for Iterated Principal Localizations

This leaf upgrades the certificate-based comparison in
`LocalizedModule.Away.Iterated` to the canonical equivalence between the
correctly based iterated localization and localization away from a product.

@stack 051T
-/

@[expose] public section

universe u v

noncomputable section

namespace LocalizedModule.Away.Iterated

variable {R : Type u} [CommSemiring R]

/-- The canonical map from the correctly based iterated localization to
localization away from `a * b`.  Its target uses the named right-handed
`Localization.Away a`-module action. -/
@[stacks 051T "iterated principal localized module canonical comparison"]
noncomputable def toMul (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] :
    letI : Module (Localization.Away a)
        (LocalizedModule.Away (a * b) M) := rightModule a b M
    Iterated a b M →ₗ[Localization.Away a]
      LocalizedModule.Away (a * b) M :=
  letI : Module (Localization.Away a)
      (LocalizedModule.Away (a * b) M) := rightModule a b M
  letI : IsScalarTower R (Localization.Away a)
      (LocalizedModule.Away (a * b) M) :=
    rightModule_isScalarTower a b M
  toMulOfUnits a b (rightModule_isUnitOn a b M)

/-- The canonical comparison from an iterated principal localization to the
product localization is bijective. -/
@[stacks 051T "iterated principal localized module canonical comparison bijectivity"]
theorem toMul_bijective (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] :
    letI : Module (Localization.Away a)
        (LocalizedModule.Away (a * b) M) := rightModule a b M
    Function.Bijective (toMul a b M) := sorry

/-- The canonical `Localization.Away a`-linear equivalence between the
correctly based iterated localization and localization away from `a * b`. -/
@[stacks 051T "iterated principal localized module product equivalence"]
noncomputable def mulEquiv (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] :
    letI : Module (Localization.Away a)
        (LocalizedModule.Away (a * b) M) := rightModule a b M
    Iterated a b M ≃ₗ[Localization.Away a]
      LocalizedModule.Away (a * b) M :=
  letI : Module (Localization.Away a)
      (LocalizedModule.Away (a * b) M) := rightModule a b M
  LinearEquiv.ofBijective (toMul a b M) (toMul_bijective a b M)

/-- The forward linear map of the canonical product equivalence is the
canonical iterated-localization comparison. -/
@[simp, stacks 051T "iterated principal localized module product equivalence map"]
theorem mulEquiv_toLinearMap (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] :
    letI : Module (Localization.Away a)
        (LocalizedModule.Away (a * b) M) := rightModule a b M
    (mulEquiv a b M).toLinearMap = toMul a b M := sorry

/-- The canonical product equivalence sends an original module element to
its canonical image in `LocalizedModule.Away (a * b) M`. -/
@[simp, stacks 051T "iterated principal localized module product equivalence application"]
theorem mulEquiv_apply_mk (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] (m : M) :
    letI : Module (Localization.Away a)
        (LocalizedModule.Away (a * b) M) := rightModule a b M
    mulEquiv a b M
        (mk a b M
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M m)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M m := sorry

/-- The canonical map to `LocalizedModule.Away (a * b) M` also presents that
module as the localization at the combined denominator submonoid. -/
@[stacks 051T "product principal localization as combined localization"]
theorem mulMk_isLocalizedModule (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] :
    IsLocalizedModule (Submonoid.powers b ⊔ Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M) := sorry

/-- The canonical base-ring-linear equivalence from successive principal
localizations first at `a` and then at `b` to localization at `a * b`. -/
@[stacks 051T "successive principal-localization product equivalence"]
noncomputable def baseMulEquiv (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] :
    LocalizedModule.Away b (LocalizedModule.Away a M) ≃ₗ[R]
      LocalizedModule.Away (a * b) M :=
  letI : IsLocalizedModule (Submonoid.powers b ⊔ Submonoid.powers a)
      (LocalizedModule.iteratedMkLinearMap
        (Submonoid.powers b) (Submonoid.powers a) M) :=
    LocalizedModule.iteratedMk_isLocalizedModule
      (Submonoid.powers b) (Submonoid.powers a) M
  letI : IsLocalizedModule (Submonoid.powers b ⊔ Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M) :=
    mulMk_isLocalizedModule a b M
  IsLocalizedModule.linearEquiv
    (Submonoid.powers b ⊔ Submonoid.powers a)
    (LocalizedModule.iteratedMkLinearMap
      (Submonoid.powers b) (Submonoid.powers a) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M)

/-- The successive-localization equivalence sends a double canonical image
to the corresponding canonical image in the product localization. -/
@[simp, stacks 051T "successive principal-localization product equivalence application"]
theorem baseMulEquiv_apply_mk (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] (m : M) :
    baseMulEquiv a b M
        (LocalizedModule.mkLinearMap (Submonoid.powers b)
          (LocalizedModule.Away a M)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M m)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M m := sorry

/-- Reindex a principal localized module along an equality of its
distinguished denominators. -/
@[stacks 051T "principal localized module denominator transport"]
noncomputable def denominatorEquiv {a b : R} (M : Type v)
    [AddCommMonoid M] [Module R M] (h : a = b) :
    LocalizedModule.Away a M ≃ₗ[R] LocalizedModule.Away b M :=
  h.rec (LinearEquiv.refl R (LocalizedModule.Away a M))

/-- Denominator transport fixes canonical localized images. -/
@[simp, stacks 051T "principal localized module denominator transport application"]
theorem denominatorEquiv_apply_mk {a b : R} (M : Type v)
    [AddCommMonoid M] [Module R M] (h : a = b) (m : M) :
    denominatorEquiv M h
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers b) M m := sorry

/-- If `P` is already a module over `Localization.Away a`, localizing its
underlying `R`-module away from `b` agrees with localizing it away from
`a * b`. -/
@[stacks 051T "already-local principal-localization product equivalence"]
noncomputable def ofLocalizedMulEquiv (a b : R) (P : Type v)
    [AddCommMonoid P] [Module R P] [Module (Localization.Away a) P]
    [IsScalarTower R (Localization.Away a) P] :
    LocalizedModule.Away b P ≃ₗ[R] LocalizedModule.Away (a * b) P :=
  letI : IsLocalizedModule (Submonoid.powers a)
      (LinearMap.id : P →ₗ[R] P) :=
    isLocalizedModule_id (Submonoid.powers a) P (Localization.Away a)
  (LocalizedModule.Away.mapEquiv b
      (LocalizedModule.Away.idLinearEquiv a).symm).trans
    (baseMulEquiv a b P)

/-- The already-local product equivalence sends a canonical image to the
canonical image with product denominator. -/
@[simp, stacks 051T "already-local principal-localization product equivalence application"]
theorem ofLocalizedMulEquiv_apply_mk (a b : R) (P : Type v)
    [AddCommMonoid P] [Module R P] [Module (Localization.Away a) P]
    [IsScalarTower R (Localization.Away a) P] (p : P) :
    ofLocalizedMulEquiv a b P
        (LocalizedModule.mkLinearMap (Submonoid.powers b) P p) =
      LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) P p := sorry

/-- Normalize the `a`-side overlap model
`(M_a)_(ab)` to the common product localization `M_(ab)`. -/
@[stacks 051T "left principal-overlap normalization"]
noncomputable def leftOverlapEquiv (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] :
    LocalizedModule.Away (a * b) (LocalizedModule.Away a M)
        ≃ₗ[Localization.Away (a * b)] LocalizedModule.Away (a * b) M :=
  let e :
      LocalizedModule.Away (a * b) (LocalizedModule.Away a M) ≃ₗ[R]
        LocalizedModule.Away (a * b) M :=
    (ofLocalizedMulEquiv a b (LocalizedModule.Away a M)).symm.trans
      (baseMulEquiv a b M)
  e.extendScalarsOfIsLocalization
    (Submonoid.powers (a * b)) (Localization.Away (a * b))

/-- The left overlap normalization sends the doubly localized canonical
image of `m` to its canonical image in `M_(ab)`. -/
@[simp, stacks 051T "left principal-overlap normalization application"]
theorem leftOverlapEquiv_apply_mk (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] (m : M) :
    leftOverlapEquiv a b M
        (LocalizedModule.mkLinearMap (Submonoid.powers (a * b))
          (LocalizedModule.Away a M)
          (LocalizedModule.mkLinearMap (Submonoid.powers a) M m)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M m := sorry

/-- Normalize the `b`-side overlap model
`(M_b)_(ab)` to the same common product localization `M_(ab)`. -/
@[stacks 051T "right principal-overlap normalization"]
noncomputable def rightOverlapEquiv (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] :
    LocalizedModule.Away (a * b) (LocalizedModule.Away b M)
        ≃ₗ[Localization.Away (a * b)] LocalizedModule.Away (a * b) M :=
  let e :
      LocalizedModule.Away (a * b) (LocalizedModule.Away b M) ≃ₗ[R]
        LocalizedModule.Away (a * b) M :=
    (denominatorEquiv (LocalizedModule.Away b M) (mul_comm a b)).trans
      (((leftOverlapEquiv b a M).restrictScalars R).trans
        (denominatorEquiv M (mul_comm b a)))
  e.extendScalarsOfIsLocalization
    (Submonoid.powers (a * b)) (Localization.Away (a * b))

/-- The right overlap normalization sends the doubly localized canonical
image of `m` to its canonical image in `M_(ab)`. -/
@[simp, stacks 051T "right principal-overlap normalization application"]
theorem rightOverlapEquiv_apply_mk (a b : R) (M : Type v)
    [AddCommMonoid M] [Module R M] (m : M) :
    rightOverlapEquiv a b M
        (LocalizedModule.mkLinearMap (Submonoid.powers (a * b))
          (LocalizedModule.Away b M)
          (LocalizedModule.mkLinearMap (Submonoid.powers b) M m)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M m := sorry

end LocalizedModule.Away.Iterated
