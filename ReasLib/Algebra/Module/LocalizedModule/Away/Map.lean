/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction Maps Between Principal Module Localizations

This leaf owns the canonical module map induced by a divisibility relation
between principal denominators.  It is expressed through Mathlib's
localization ring map and tensor-product model, so it does not require a
chosen localization instance on the target module.
-/

@[expose] public section

universe u v w

namespace LocalizedModule.Away

variable {R : Type u} [CommSemiring R]

/- The unit criterion is the intrinsic algebraic form of an inclusion of
principal opens.  Divisibility is only one convenient sufficient condition. -/
/-- If the image of `a` is a unit in `R_b`, restriction along the corresponding
inclusion of principal opens maps `M_a` to `M_b`. -/
@[stacks 00EK "principal localized module restriction by a unit criterion"]
noncomputable def mapOfIsUnit
    {M : Type v} [AddCommMonoid M] [Module R M]
    (a b : R) (h : IsUnit (algebraMap R (Localization.Away b) a)) :
    LocalizedModule.Away a M →ₗ[R] LocalizedModule.Away b M :=
  ((LocalizedModule.equivTensorProduct (Submonoid.powers b) M).symm.toLinearMap.restrictScalars R) ∘ₗ
    (TensorProduct.map
      (IsLocalization.Away.liftAlgHom
        (A := R) (S := Localization.Away a) (P := Localization.Away b)
        (f := Algebra.ofId R (Localization.Away b)) a h).toLinearMap
      (LinearMap.id)) ∘ₗ
      ((LocalizedModule.equivTensorProduct (Submonoid.powers a) M).toLinearMap.restrictScalars R)

/-- If `a ∣ b`, restriction along `D(b) ≤ D(a)` maps the
localization of `M` away from `a` to the localization away from `b`. -/
@[stacks 00EK "principal localized module restriction"]
noncomputable def mapOfDvd
    {M : Type v} [AddCommMonoid M] [Module R M]
  (a b : R) (h : a ∣ b) :
    LocalizedModule.Away a M →ₗ[R] LocalizedModule.Away b M :=
  mapOfIsUnit a b (IsLocalization.Away.isUnit_of_dvd b h)

/-- The canonical map from the principal localization of a module
away from an element of `S` to its localization at all of `S`. -/
@[stacks 00CR "principal localized module to total localization"]
noncomputable def toLocalizedModule
    {M : Type v} [AddCommMonoid M] [Module R M]
    (S : Submonoid R) (s : S) :
    LocalizedModule.Away (s : R) M →ₗ[R] LocalizedModule S M :=
  LocalizedModule.liftOfLE (Submonoid.powers (s : R)) S
    (Submonoid.powers_le.2 s.2)

/-- The canonical map from a principal localization to the total localization
sends an original module element to its total localized image. -/
@[simp, stacks 00CR "principal localized module to total localization application"]
theorem toLocalizedModule_apply_mk
    {M : Type v} [AddCommMonoid M] [Module R M]
    (S : Submonoid R) (s : S) (m : M) :
    toLocalizedModule (M := M) S s
        (LocalizedModule.mkLinearMap (Submonoid.powers (s : R)) M m) =
      LocalizedModule.mkLinearMap S M m := sorry

/-- Canonical maps from principal localizations to the total
localization are compatible with divisibility restrictions. -/
@[stacks 00CR "principal localized module total-localization naturality"]
theorem toLocalizedModule_naturality
    {M : Type v} [AddCommMonoid M] [Module R M]
    (S : Submonoid R) (a b : S) (h : (a : R) ∣ (b : R)) :
    (toLocalizedModule (M := M) S b).comp
        (mapOfDvd (M := M) (a : R) (b : R) h) =
      toLocalizedModule (M := M) S a := sorry

/-- The base-ring-linear view of the map induced between two
modules localized away from the same element.  The stronger
`Localization.Away r`-linear map is `LocalizedModule.map (Submonoid.powers r) g`. -/
@[stacks 051T "principal localized linear map"]
noncomputable def map
    {M : Type v} {N : Type w} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (r : R) (g : M →ₗ[R] N) :
    LocalizedModule.Away r M →ₗ[R] LocalizedModule.Away r N :=
  (LocalizedModule.map (Submonoid.powers r) g).restrictScalars R

/-- The principal-localized map applies its source map to the numerator of a
canonical localized element. -/
@[simp, stacks 051T "principal localized linear map application"]
theorem map_apply_mk
    {M : Type v} {N : Type w} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (r : R) (g : M →ₗ[R] N) (m : M) :
    map r g (LocalizedModule.mkLinearMap (Submonoid.powers r) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers r) N (g m) := sorry

/-- Localizing the identity map away from `r` gives the identity. -/
@[simp, stacks 051T "principal localized linear map identity"]
theorem map_id
    {M : Type v} [AddCommMonoid M] [Module R M] (r : R) :
    map r (LinearMap.id : M →ₗ[R] M) = LinearMap.id := sorry

/-- Localizing a composite away from `r` is the composite of the
localized maps. -/
@[simp, stacks 051T "principal localized linear map composition"]
theorem map_comp
    {M : Type v} {N : Type w} {P : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    (r : R) (g : M →ₗ[R] N) (h : N →ₗ[R] P) :
    map r (h.comp g) = (map r h).comp (map r g) := sorry

/-- Principal-localization restriction induced by a unit criterion sends a
canonical localized element to the corresponding canonical element. -/
@[simp, stacks 00EK "principal localized module unit restriction application"]
theorem mapOfIsUnit_apply_mk
    {M : Type v} [AddCommMonoid M] [Module R M]
    (a b : R) (h : IsUnit (algebraMap R (Localization.Away b) a)) (m : M) :
    mapOfIsUnit a b h
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers b) M m := sorry

/-- Principal-localization restriction sends a canonical localized element to
the same canonical element in the smaller principal open. -/
@[simp, stacks 00EK "principal localized module restriction application"]
theorem mapOfDvd_apply_mk
    {M : Type v} [AddCommMonoid M] [Module R M]
    (a b : R) (h : a ∣ b) (m : M) :
    mapOfDvd a b h
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M m) =
      LocalizedModule.mkLinearMap (Submonoid.powers b) M m := sorry

/-- When `b = a * r`, restriction from `LocalizedModule.Away a M` to
`LocalizedModule.Away b M` sends a power-denominator
fraction to the corresponding fraction with numerator multiplied by `r ^ n`. -/
@[simp, stacks 00CR "principal localization power-denominator formula"]
theorem mapOfDvd_apply_mk_pow
    {M : Type v} [AddCommMonoid M] [Module R M]
    (a b : R) {r : R} (hr : b = a * r) (n : ℕ) (m : M) :
    mapOfDvd a b ⟨r, hr⟩ (LocalizedModule.mk m (Submonoid.pow a n)) =
      LocalizedModule.mk (r ^ n • m) (Submonoid.pow b n) := sorry

/-- Restriction from a principal localization to itself is the
identity when expressed by any unit witness. -/
@[simp, stacks 00EK "principal localized module unit restriction identity"]
theorem mapOfIsUnit_self
    {M : Type v} [AddCommMonoid M] [Module R M]
    (a : R) (h : IsUnit (algebraMap R (Localization.Away a) a)) :
    mapOfIsUnit (M := M) a a h = LinearMap.id := sorry

/-- Compatible principal-localization restrictions compose to the
direct restriction.  The explicit `h_ac` records the unit criterion for that
direct restriction. -/
@[stacks 00EK "principal localized module unit restriction composition"]
theorem mapOfIsUnit_comp
    {M : Type v} [AddCommMonoid M] [Module R M]
    (a b c : R) (h_ab : IsUnit (algebraMap R (Localization.Away b) a))
    (h_bc : IsUnit (algebraMap R (Localization.Away c) b))
    (h_ac : IsUnit (algebraMap R (Localization.Away c) a)) :
    (mapOfIsUnit (M := M) b c h_bc).comp (mapOfIsUnit (M := M) a b h_ab) =
      mapOfIsUnit (M := M) a c h_ac := sorry

/-- Restriction of localized modules is natural in the underlying
`R`-linear map. -/
@[stacks 00EK "principal localized module restriction naturality"]
theorem mapOfIsUnit_naturality
    {M : Type v} {N : Type w} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (a b : R)
    (h : IsUnit (algebraMap R (Localization.Away b) a)) (g : M →ₗ[R] N) :
    (map b g).comp (mapOfIsUnit (M := M) a b h) =
      (mapOfIsUnit (M := N) a b h).comp (map a g) := sorry

/-- The divisibility restriction from a principal localization to
itself is the identity. -/
@[simp, stacks 00EK "principal localized module restriction identity"]
theorem mapOfDvd_refl
    {M : Type v} [AddCommMonoid M] [Module R M] (a : R) :
    mapOfDvd (M := M) a a (dvd_refl a) = LinearMap.id := sorry

/-- Restrictions induced by two divisibility relations compose to
the restriction induced by their composite. -/
@[stacks 00EK "principal localized module restriction composition"]
theorem mapOfDvd_comp
    {M : Type v} [AddCommMonoid M] [Module R M]
    (a b c : R) (h_ab : a ∣ b) (h_bc : b ∣ c) :
    (mapOfDvd (M := M) b c h_bc).comp (mapOfDvd (M := M) a b h_ab) =
      mapOfDvd (M := M) a c (h_ab.trans h_bc) := sorry

end LocalizedModule.Away
