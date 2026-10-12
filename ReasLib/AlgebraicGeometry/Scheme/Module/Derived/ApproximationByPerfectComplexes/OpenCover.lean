/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PerfectApproximation.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ApproximationByPerfectComplexes.Affine

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes

/-- If a scheme is covered by a quasi-compact open and an affine open whose intersection
is quasi-compact, approximation by perfect complexes on the first open implies approximation
by perfect complexes on the scheme. -/
theorem of_union {X : Scheme.{u}} (U : X.Opens) (V : X.affineOpens)
    (h_cover : U ⊔ V = ⊤) (hU_compact : IsCompact (U : Set X))
    (hUV_compact : IsCompact ((U ⊓ V : X.Opens) : Set X))
    (hU : HasApproximationByPerfectComplexes U.toScheme) :
    HasApproximationByPerfectComplexes X := sorry

end AlgebraicGeometry.Scheme.HasApproximationByPerfectComplexes
