module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernels of localized linear maps

This leaf gives the canonical-map specialization of Mathlib's general theorem
that localization commutes with kernels.  The specialization avoids exposing
the implementation of `LocalizedModule.map` to downstream users.
-/

@[expose] public section

universe u v w

namespace LinearMap

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Tag `051T`: the kernel of the canonical localization of a linear map is
the localization of its source kernel. -/
@[stacks 051T "localized linear-map kernel"]
theorem localizedKer_eq_ker_map (T : Submonoid R) (f : M →ₗ[R] N) :
    (ker f).localized T = ker (LocalizedModule.map T f) := sorry

/-- Tag `05N6`: the range of the localized inclusion of a kernel is the
kernel of the localized map.  This packages the composable image form of
`localizedKer_eq_ker_map`. -/
@[stacks 05N6 "localized kernel inclusion range"]
theorem range_localizedKerSubtype_eq_ker_map (T : Submonoid R) (f : M →ₗ[R] N) :
    range (LocalizedModule.map T (ker f).subtype) =
      ker (LocalizedModule.map T f) := sorry

end LinearMap

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Tag `061Q`: over a ring, the canonical localization of a linear map is injective exactly when
the localization of its kernel is trivial.  Additive inverses are essential for this equivalence. -/
@[stacks 061Q "localized map injectivity criterion"]
theorem localizedMap_injective_iff (T : Submonoid R) (f : M →ₗ[R] N) :
    Function.Injective (LocalizedModule.map T f) ↔
      Subsingleton (LocalizedModule T (ker f)) := sorry

end LinearMap
