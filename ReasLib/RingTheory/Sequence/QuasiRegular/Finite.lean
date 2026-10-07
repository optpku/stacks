module

public import ReasLib.Algebra.Module.LocalizedModule.Finite
public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic

/-!
# Finite Kernels for Quasi-Regular Comparison Maps

@stack 061Q

The comparison kernel is named independently of localization.  Its canonical
restricted scalar structure and finite-generation theorem are reusable by any
argument that studies quasi-regularity through vanishing of this kernel.
-/

@[expose] public section

noncomputable section

universe u v

namespace RingTheory.Sequence.QuasiRegular

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The polynomial coefficient ring acting on the quasi-regular comparison
map attached to `rs`. -/
@[stacks 061Q "quasi-regular comparison coefficient ring"]
abbrev coefficientRing (rs : List R) :=
  MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)

/-- The kernel of the associated-graded comparison map for `rs` on `M`. -/
@[stacks 061Q "quasi-regular comparison kernel"]
abbrev comparisonKernel (rs : List R) :=
  LinearMap.ker (comparisonMap (M := M) rs)

/-- The comparison kernel carries the canonical `R`-module structure obtained
by restricting its polynomial coefficient-ring action. -/
noncomputable instance comparisonKernelModule (rs : List R) :
    Module R (comparisonKernel (M := M) rs) :=
  Module.restrictScalars R (coefficientRing rs) (comparisonKernel (M := M) rs)

/-- The restricted `R`-action on the comparison kernel is compatible with its
polynomial coefficient-ring action. -/
instance comparisonKernelIsScalarTower (rs : List R) :
    IsScalarTower R (coefficientRing rs) (comparisonKernel (M := M) rs) := sorry

/-- Tag `061Q`: over a Noetherian ring, the comparison kernel of a finite
module is finite over the polynomial coefficient ring. -/
@[stacks 061Q "finite quasi-regular comparison kernel"]
theorem comparisonKernel_finite [IsNoetherianRing R] [Module.Finite R M]
    (rs : List R) :
    Module.Finite (coefficientRing rs) (comparisonKernel (M := M) rs) := sorry

end RingTheory.Sequence.QuasiRegular
