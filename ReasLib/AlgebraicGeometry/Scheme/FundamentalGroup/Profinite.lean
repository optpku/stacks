module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Fiber
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The profinite fundamental group of a connected scheme at a geometric point is
the automorphism group of its finite étale fiber functor, equipped with the
canonical profinite topology. -/
noncomputable def profiniteFundamentalGroup {X : Scheme.{u}} [ConnectedSpace X]
    {K : Type u} [Field K] [IsAlgClosed K] (point : Spec (.of K) ⟶ X) :
    ProfiniteGrp.{u + 1} :=
  ProfiniteGrp.of (Scheme.fundamentalGroup point)

end AlgebraicGeometry.Scheme
