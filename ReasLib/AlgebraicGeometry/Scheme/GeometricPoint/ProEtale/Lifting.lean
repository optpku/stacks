/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Point
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.Family
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber

open AlgebraicGeometry CategoryTheory Scheme

universe u v

@[expose] public section

namespace AlgebraicGeometry.Scheme.GeometricPoint

/-- A geometric point lifts through some member of an indexed pro-étale covering
family, with the same source field. -/
theorem exists_lift_of_proetaleCovering {S : Scheme.{u}} (s : GeometricPoint S)
    {ι : Type v} (family : ι → Over S) (hcover : Scheme.Proetale.IsCovering family) :
    ∃ (i : ι) (s_i : Spec (.of s.K) ⟶ (family i).left),
      s_i ≫ (family i).hom = s.hom := sorry

/-- A geometric point lifts through some member of a fixed-target pro-étale cover,
with the same source field. -/
theorem exists_lift_of_proetaleCover {S : Scheme.{u}} (s : GeometricPoint S)
    (𝒰 : S.Cover Scheme.proetalePrecoverage) :
    ∃ (i : 𝒰.I₀) (s_i : Spec (.of s.K) ⟶ 𝒰.X i), s_i ≫ 𝒰.f i = s.hom := sorry

end AlgebraicGeometry.Scheme.GeometricPoint
