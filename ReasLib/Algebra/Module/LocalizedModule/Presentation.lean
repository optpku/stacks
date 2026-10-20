/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Quotient
public import ReasLib.Algebra.Module.LocalizedModule.Kernel
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localized Quotient Presentations

This leaf packages the quotient comparison attached to a presentation map.
When a relation submodule becomes the kernel after localization, a surjective
localized presentation induces a canonical equivalence from the localized
source quotient to the localized target.

@stack 05N6
-/

@[expose] public section

universe u v w

namespace Submodule

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Tag `05N6`: a relation submodule has the localized presentation kernel
whenever it agrees with the localization of the source kernel. This is the
presentation-facing form of `LinearMap.localizedKer_eq_ker_map`. -/
@[stacks 05N6 "localized relation kernel"]
theorem localized_eq_ker_map_of_eq_localizedKer
    (S : Submonoid R) (K : Submodule R M) (f : M →ₗ[R] N)
    (h_kernel : K.localized S = (LinearMap.ker f).localized S) :
    K.localized S = LinearMap.ker (LocalizedModule.map S f) := sorry

end Submodule

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Tag `05N6`: a surjective localized presentation with a specified equality
between the localized relation submodule and its localized kernel induces a
canonical equivalence from the localized source quotient to the localized
target. -/
@[stacks 05N6 "localized quotient presentation equivalence"]
noncomputable def localizedQuotientEquiv
    (S : Submonoid R) (f : M →ₗ[R] N) (K : Submodule R M)
    (h_surjective : Function.Surjective (LocalizedModule.map S f))
    (h_localizedKer : K.localized S = LinearMap.ker (LocalizedModule.map S f)) :
    LocalizedModule S (M ⧸ K) ≃ₗ[Localization S] LocalizedModule S N :=
  (_root_.localizedQuotientEquiv S K).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ h_localizedKer ≪≫ₗ
    (LocalizedModule.map S f).quotKerEquivOfSurjective h_surjective

/-- The localized quotient-presentation equivalence sends the class of a
source generator to the localized value of the presentation map whenever its
localized relation submodule is specified as the localized kernel. -/
@[simp, stacks 05N6 "localized quotient presentation equivalence application"]
theorem localizedQuotientEquiv_apply_mk
    (S : Submonoid R) (f : M →ₗ[R] N) (K : Submodule R M)
    (h_surjective : Function.Surjective (LocalizedModule.map S f))
    (h_localizedKer : K.localized S = LinearMap.ker (LocalizedModule.map S f))
    (x : M) :
    localizedQuotientEquiv S f K h_surjective h_localizedKer
        (LocalizedModule.mkLinearMap S (M ⧸ K) (Submodule.Quotient.mk x)) =
      LocalizedModule.mkLinearMap S N (f x) := sorry

/-- If a map from the source quotient agrees with a presentation map before
quotienting, its localized map is the canonical quotient-presentation
equivalence under a specified localized-kernel equality. -/
@[stacks 05N6 "localized quotient presentation comparison"]
theorem localizedQuotientEquiv_toLinearMap
    (S : Submonoid R) (f : M →ₗ[R] N) (K : Submodule R M)
    (h_surjective : Function.Surjective (LocalizedModule.map S f))
    (h_localizedKer : K.localized S = LinearMap.ker (LocalizedModule.map S f))
    (g : M ⧸ K →ₗ[R] N)
    (h_comp : g.comp (Submodule.mkQ K) = f) :
    (localizedQuotientEquiv S f K h_surjective h_localizedKer).toLinearMap =
      LocalizedModule.map S g := sorry

end LinearMap
