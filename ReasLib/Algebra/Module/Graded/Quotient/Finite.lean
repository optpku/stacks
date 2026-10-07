module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import ReasLib.Algebra.Module.Graded.Quotient.RestrictScalars
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite homogeneous pieces of restricted-scalar quotients

This leaf isolates the linear-algebraic part of the usual graded-submodule argument.  A grading is
recorded over a base ring `R`, while the submodule defining the quotient may be owned by a larger
ring `S`.  The quotient component is the range of the restricted quotient map, and the source
component splits into its intersection with the submodule and that range.

The statements are intentionally indexed one component at a time.  Consumers that know finiteness
for a whole family can pass the corresponding component instance, without rebuilding local
instances or importing a polynomial/Hilbert-function layer.
-/

@[expose] public section

noncomputable section

universe u v w x

namespace DirectSum.Decomposition

variable {ι : Type u} [DecidableEq ι]
variable {R : Type v} [Ring R]
variable {S : Type w} [Ring S] [SMul R S]
variable {M : Type x} [AddCommGroup M] [Module R M] [Module S M]
variable [IsScalarTower R S M]

namespace quotientGradingRestrictScalars

/-- Stacks 052N: a restricted-scalar quotient component is the range of the quotient map on the
corresponding source component.  This is the canonical bridge from graded quotient notation to
rank-nullity APIs for linear maps. -/
@[stacks 052N "restricted-scalar quotient component as a restricted-map range"]
theorem eq_range
    (𝒜 : ι → Submodule R M) (P : Submodule S M) (i : ι) :
    quotientGradingRestrictScalars 𝒜 P i =
      LinearMap.range ((P.mkQ.restrictScalars R).domRestrict (𝒜 i)) := sorry

/-- Stacks 052N: the image of the degree-`i` part of a submodule and the image of the kernel of
the restricted quotient map are the same ambient submodule.  Both sides model the intersection
of the source component with the quotient submodule, but retain their native subtype owners. -/
@[stacks 052N "intersection represented by the restricted quotient kernel"]
theorem comap_map_eq_kernel_map
    (𝒜 : ι → Submodule R M) (P : Submodule S M) (i : ι) :
    ((𝒜 i).comap ((P.restrictScalars R).subtype)).map
          ((P.restrictScalars R).subtype) =
      (LinearMap.ker ((P.mkQ.restrictScalars R).domRestrict (𝒜 i))).map
          (𝒜 i).subtype := sorry

/-- Stacks 052N: finite-dimensionality of a source component passes to the corresponding
restricted-scalar quotient component. -/
@[stacks 052N "finite restricted-scalar quotient component"]
theorem moduleFinite
    (𝒜 : ι → Submodule R M) (P : Submodule S M) (i : ι)
    (hfinite : Module.Finite R (𝒜 i)) :
    Module.Finite R (quotientGradingRestrictScalars 𝒜 P i) := sorry

/-- Stacks 052N: finite-dimensionality of a source component passes to its intersection with a
larger-scalar submodule, represented as a comap along the submodule inclusion. The Noetherian
hypothesis is essential here: finite generation is not inherited by arbitrary submodules over a
general ring. -/
@[stacks 052N "finite restricted-scalar submodule component"]
theorem comap_moduleFinite
    (𝒜 : ι → Submodule R M) (P : Submodule S M) (i : ι)
    [IsNoetherianRing R]
    (hfinite : Module.Finite R (𝒜 i)) :
    Module.Finite R ((𝒜 i).comap ((P.restrictScalars R).subtype)) := sorry

end quotientGradingRestrictScalars

end DirectSum.Decomposition

namespace DirectSum.Decomposition

section Finrank

variable {ι : Type u} [DecidableEq ι]
variable {R : Type v} [DivisionRing R]
variable {S : Type w} [Ring S] [SMul R S]
variable {M : Type x} [AddCommGroup M] [Module R M] [Module S M]
variable [IsScalarTower R S M]

namespace quotientGradingRestrictScalars

/-- Stacks 052N: rank-nullity for one homogeneous component of a restricted-scalar quotient.

The source component is finite-dimensional over `R`; its rank is the sum of the rank of the
intersection with `P` and the rank of the corresponding quotient component.  This Nat-valued form
is the primary reusable statement. -/
@[stacks 052N "rank-nullity for a restricted-scalar quotient component"]
theorem finrank_add
    (𝒜 : ι → Submodule R M) (P : Submodule S M) (i : ι)
    (hfinite : Module.Finite R (𝒜 i)) :
    Module.finrank R (𝒜 i) =
      Module.finrank R ((𝒜 i).comap ((P.restrictScalars R).subtype)) +
        Module.finrank R (quotientGradingRestrictScalars 𝒜 P i) := sorry

/-- Stacks 052N: the integer-valued rank-nullity bridge for a restricted-scalar quotient component.
This is a coercion-friendly companion for Hilbert-polynomial calculations; the Nat-valued
`finrank_add` theorem is the canonical linear-algebra API. -/
@[stacks 052N "integer rank-nullity bridge for a restricted-scalar quotient component"]
theorem finrank_add_int
    (𝒜 : ι → Submodule R M) (P : Submodule S M) (i : ι)
    (hfinite : Module.Finite R (𝒜 i)) :
    (Module.finrank R (𝒜 i) : ℤ) =
      (Module.finrank R ((𝒜 i).comap ((P.restrictScalars R).subtype)) : ℤ) +
        (Module.finrank R (quotientGradingRestrictScalars 𝒜 P i) : ℤ) := sorry

end quotientGradingRestrictScalars

end Finrank

end DirectSum.Decomposition
