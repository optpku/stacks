module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The dimension of a finite-type scheme over a field is attained as the maximum of the
dimensions of its affine opens. -/
theorem isGreatest_topologicalKrullDim_affineOpens
    {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X] :
    IsGreatest
      {d : WithBot ℕ∞ |
        ∃ U : X.left.affineOpens, d = topologicalKrullDim (U : Set X.left)}
      (topologicalKrullDim X.left) := sorry

/-- The dimension of a finite-type scheme over a field is the indexed supremum of the
dimensions of its affine opens. -/
theorem topologicalKrullDim_eq_iSup_affineOpens
    {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X] :
    topologicalKrullDim X.left =
      ⨆ U : X.left.affineOpens, topologicalKrullDim (U : Set X.left) := sorry

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry.Scheme

/-- The topological Krull dimension of an affine scheme is the Krull dimension of its
ring of global sections. -/
theorem topologicalKrullDim_eq_ringKrullDim_of_isAffine
    (X : Scheme.{u}) [IsAffine X] :
    topologicalKrullDim X = ringKrullDim Γ(X, ⊤) := sorry

end AlgebraicGeometry.Scheme
