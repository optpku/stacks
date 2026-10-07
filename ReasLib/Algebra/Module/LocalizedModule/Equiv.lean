module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences of Localized Modules

Mathlib's `IsLocalizedModule.mapEquiv` treats arbitrary models of a module
localization.  This leaf provides the canonical-model interface and the
principal-localization view needed when comparisons are composed only over
the original base ring.
-/

@[expose] public section

universe u v w x

namespace LocalizedModule

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- The canonical localization of the self-module `R` is the localized ring. -/
@[stacks 051T "self-localization equivalence"]
noncomputable def selfEquiv (S : Submonoid R) :
    LocalizedModule S R ≃ₗ[Localization S] Localization S :=
  (LocalizedModule.equivTensorProduct S R).trans
    (Algebra.TensorProduct.rid R (Localization S) (Localization S)).toLinearEquiv

/-- The self-localization equivalence sends a denominator presentation to the corresponding
localized-ring fraction. -/
@[simp, stacks 051T "self-localization equivalence application"]
theorem selfEquiv_apply_mk (S : Submonoid R) (r : R) (s : S) :
    selfEquiv S (LocalizedModule.mk r s) = Localization.mk r s := sorry

/-- An `R`-linear equivalence induces the canonical equivalence between its
localizations at a common submonoid. -/
@[stacks 051T "localized linear equivalence"]
noncomputable def mapEquiv (S : Submonoid R) (e : M ≃ₗ[R] N) :
    LocalizedModule S M ≃ₗ[Localization S] LocalizedModule S N :=
  IsLocalizedModule.mapEquiv S
    (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N)
    (Localization S) e

/-- The forward map of the canonical localized equivalence is the localization
of the forward map. -/
@[simp, stacks 051T "localized linear equivalence map"]
theorem mapEquiv_toLinearMap (S : Submonoid R) (e : M ≃ₗ[R] N) :
    (mapEquiv S e).toLinearMap = LocalizedModule.map S e.toLinearMap := sorry

/-- The canonical localized equivalence applies an original linear equivalence
to the numerator of every localized element. -/
@[simp, stacks 051T "localized linear equivalence application"]
theorem mapEquiv_apply_mk (S : Submonoid R) (e : M ≃ₗ[R] N)
    (m : M) (s : S) :
    mapEquiv S e (LocalizedModule.mk m s) = LocalizedModule.mk (e m) s := sorry

/-- The inverse canonical localized equivalence applies the inverse original
linear equivalence to the numerator of every localized element. -/
@[simp, stacks 051T "inverse localized linear equivalence application"]
theorem mapEquiv_symm_apply_mk (S : Submonoid R) (e : M ≃ₗ[R] N)
    (n : N) (s : S) :
    (mapEquiv S e).symm (LocalizedModule.mk n s) = LocalizedModule.mk (e.symm n) s := sorry

/-- A bijective canonical map between localized modules is its canonical
linear equivalence. -/
@[stacks 051T "bijective localized linear map equivalence"]
noncomputable def mapEquivOfBijective (T : Submonoid R) (f : M →ₗ[R] N)
    (h : Function.Bijective (LocalizedModule.map T f)) :
    LocalizedModule T M ≃ₗ[Localization T] LocalizedModule T N :=
  LinearEquiv.ofBijective (LocalizedModule.map T f) h

/-- The forward linear map of `mapEquivOfBijective` is the canonical localized map. -/
@[simp, stacks 051T "bijective localized linear map equivalence map"]
theorem mapEquivOfBijective_toLinearMap (T : Submonoid R) (f : M →ₗ[R] N)
    (h : Function.Bijective (LocalizedModule.map T f)) :
    (mapEquivOfBijective T f h).toLinearMap = LocalizedModule.map T f := sorry

/-- The equivalence induced by a bijective localized map acts by that localized map. -/
@[simp, stacks 051T "bijective localized linear map equivalence application"]
theorem mapEquivOfBijective_apply (T : Submonoid R) (f : M →ₗ[R] N)
    (h : Function.Bijective (LocalizedModule.map T f)) (x : LocalizedModule T M) :
    mapEquivOfBijective T f h x = LocalizedModule.map T f x := sorry

namespace Away

/-- The base-ring-linear view of the equivalence induced between two
localizations away from the same element.  The stronger
`Localization.Away r`-linear equivalence is `LocalizedModule.mapEquiv
(Submonoid.powers r) e`. -/
@[stacks 051T "principal localized linear equivalence"]
noncomputable def mapEquiv (r : R) (e : M ≃ₗ[R] N) :
    LocalizedModule.Away r M ≃ₗ[R] LocalizedModule.Away r N :=
  (LocalizedModule.mapEquiv (Submonoid.powers r) e).restrictScalars R

/-- The principal-localization equivalence sends a canonical localized element
to the canonical localized image of its numerator. -/
@[simp, stacks 051T "principal localized linear equivalence application"]
theorem mapEquiv_apply_mk (r : R) (e : M ≃ₗ[R] N) (m : M) :
    mapEquiv r e (LocalizedModule.mk m 1) = LocalizedModule.mk (e m) 1 := sorry

/-- The inverse principal-localization equivalence sends a canonical localized
element to the canonical localized inverse image of its numerator. -/
@[simp, stacks 051T "inverse principal localized linear equivalence application"]
theorem mapEquiv_symm_apply_mk (r : R) (e : M ≃ₗ[R] N) (n : N) :
    (mapEquiv r e).symm (LocalizedModule.mk n 1) = LocalizedModule.mk (e.symm n) 1 := sorry

end Away

end LocalizedModule

namespace IsLocalizedModule

variable {R : Type u} [CommSemiring R]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- A localized-module model has a canonical direct linear equivalence with the
localized module over the localization ring.  The explicit proof argument keeps
the owner usable without installing a global `IsLocalizedModule` instance for a
temporary map. -/
@[stacks 087P "localized-module model equivalence"]
noncomputable def localizedEquiv
    (S : Submonoid R) (A : Type x) [CommSemiring A] [Algebra R A]
    [IsLocalization S A] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) (h : IsLocalizedModule S f) :
    -- Local instance justification (defeq pin): the explicit proof must be used in the type.
    letI : IsLocalizedModule S f := h
    -- Local instance justification (defeq pin): use the canonical localized module action.
    letI : Module A (LocalizedModule S M) :=
      IsLocalizedModule.module S (LocalizedModule.mkLinearMap S M)
    -- Local instance justification (defeq pin): use the scalar tower attached to that action.
    letI : IsScalarTower R A (LocalizedModule S M) :=
      IsLocalizedModule.isScalarTower_module S (LocalizedModule.mkLinearMap S M)
    LocalizedModule S M ≃ₗ[A] N :=
  -- Mathlib deliberately keeps the `A`-module structure and its scalar tower on the
  -- canonical localized module non-global; pin the canonical pair at this owner boundary.
  -- Local instance justification (defeq pin): the equivalence is indexed by this proof.
  letI : IsLocalizedModule S f := h
  -- Local instance justification (defeq pin): retain the canonical localized module action.
  letI : Module A (LocalizedModule S M) :=
    IsLocalizedModule.module S (LocalizedModule.mkLinearMap S M)
  -- Local instance justification (defeq pin): retain the matching scalar tower.
  letI : IsScalarTower R A (LocalizedModule S M) :=
    IsLocalizedModule.isScalarTower_module S (LocalizedModule.mkLinearMap S M)
  (IsLocalizedModule.iso S f).extendScalarsOfIsLocalization S A

/-- The localized-module model equivalence agrees with the model map on
canonical generators. -/
@[simp, stacks 087P "localized-module model equivalence on generators"]
theorem localizedEquiv_apply_mk
    (S : Submonoid R) (A : Type x) [CommSemiring A] [Algebra R A]
    [IsLocalization S A] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) (h : IsLocalizedModule S f) (m : M) (s : S) :
    localizedEquiv S A f h (LocalizedModule.mk m s) =
      (h.map_units s).unit⁻¹.val (f m) := sorry

end IsLocalizedModule
