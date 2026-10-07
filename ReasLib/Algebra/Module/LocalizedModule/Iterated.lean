module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Iterated Localizations of Modules

This leaf owns the canonical map from a module localized successively at two
submonoids to the localization at their supremum.  It deliberately separates
that concrete map from the proposition that it is an equivalence, so no
unproved localization property is installed as a global instance.

@stack 051T
-/

@[expose] public section

universe u v

namespace LocalizedModule

variable {R : Type u} [CommSemiring R]

/-- Tag `051T`: the canonical map from a module to its localization first at
`T` and then at `S`. -/
@[stacks 051T "iterated localized module map"]
noncomputable def iteratedMkLinearMap
    (S T : Submonoid R) (M : Type v) [AddCommMonoid M] [Module R M] :
    M →ₗ[R] LocalizedModule S (LocalizedModule T M) :=
  (LocalizedModule.mkLinearMap S (LocalizedModule T M)).comp
    (LocalizedModule.mkLinearMap T M)

/-- Tag `051T`: the canonical comparison from a module localized first at
`T` and then at `S` to its localization at `S ⊔ T`. -/
@[stacks 051T "iterated localized module comparison"]
noncomputable def iteratedToSup
    (S T : Submonoid R) (M : Type v) [AddCommMonoid M] [Module R M] :
    LocalizedModule S (LocalizedModule T M) →ₗ[R] LocalizedModule (S ⊔ T) M :=
  LocalizedModule.lift S
    (LocalizedModule.liftOfLE T (S ⊔ T) (le_sup_right : T ≤ S ⊔ T))
      (fun s ↦ IsLocalizedModule.map_units
      (LocalizedModule.mkLinearMap (S ⊔ T) M)
      ⟨s.1, (le_sup_left : S ≤ S ⊔ T) s.2⟩)

/-- Tag `051T`: the linear equivalence from an iterated localization to the
localization at the supremum, constructed from an explicitly supplied
bijectivity witness. -/
@[stacks 051T "iterated localized module comparison equivalence"]
noncomputable def iteratedToSupEquiv
    (S T : Submonoid R) {M : Type v} [AddCommMonoid M] [Module R M]
    (h : Function.Bijective (iteratedToSup S T M)) :
    LocalizedModule S (LocalizedModule T M) ≃ₗ[R] LocalizedModule (S ⊔ T) M :=
  LinearEquiv.ofBijective (iteratedToSup S T M) h

/-- The forward linear map of `iteratedToSupEquiv` is the canonical comparison
map from which it is constructed. -/
@[simp, stacks 051T "iterated localized module comparison equivalence map"]
theorem iteratedToSupEquiv_toLinearMap
    (S T : Submonoid R) {M : Type v} [AddCommMonoid M] [Module R M]
    (h : Function.Bijective (iteratedToSup S T M)) :
    (iteratedToSupEquiv S T h).toLinearMap = iteratedToSup S T M := sorry

/-- Applying `iteratedToSupEquiv` agrees with the canonical comparison map. -/
@[simp, stacks 051T "iterated localized module comparison equivalence application"]
theorem iteratedToSupEquiv_apply
    (S T : Submonoid R) {M : Type v} [AddCommMonoid M] [Module R M]
    (h : Function.Bijective (iteratedToSup S T M))
    (x : LocalizedModule S (LocalizedModule T M)) :
    iteratedToSupEquiv S T h x = iteratedToSup S T M x := sorry

/-- Tag `051T`: the iterated canonical localization map has the universal
property of localization at the combined denominator submonoid. -/
@[stacks 051T "iterated localized module property"]
theorem iteratedMk_isLocalizedModule
    (S T : Submonoid R) (M : Type v) [AddCommMonoid M] [Module R M] :
    IsLocalizedModule (S ⊔ T) (iteratedMkLinearMap S T M) := sorry

/-- The comparison to the supremum localization agrees with the canonical
localization map on the original module. -/
@[stacks 051T "iterated localized module comparison composition"]
theorem iteratedToSup_comp
    (S T : Submonoid R) (M : Type v) [AddCommMonoid M] [Module R M] :
    (iteratedToSup S T M).comp (iteratedMkLinearMap S T M) =
      LocalizedModule.mkLinearMap (S ⊔ T) M := sorry

/-- The comparison to the supremum localization sends a canonical iterated
image to the corresponding canonical image at `S ⊔ T`. -/
@[simp, stacks 051T "iterated localized module comparison application"]
theorem iteratedToSup_apply_iteratedMk
    (S T : Submonoid R) (M : Type v) [AddCommMonoid M] [Module R M] (m : M) :
    iteratedToSup S T M (iteratedMkLinearMap S T M m) =
      LocalizedModule.mkLinearMap (S ⊔ T) M m := sorry

/-- Tag `051T`: the canonical comparison from an iterated localization to the
localization at the supremum is bijective. -/
@[stacks 051T "iterated localized module comparison bijective"]
theorem iteratedToSup_bijective
    (S T : Submonoid R) (M : Type v) [AddCommMonoid M] [Module R M] :
    Function.Bijective (iteratedToSup S T M) := sorry

end LocalizedModule
