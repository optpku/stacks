/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberRank
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Degrees of finite locally free modules on proper curves

The rank of a finite locally free module on a proper curve is read from its generic fiber, giving
a degree operation which does not require callers to provide a rank separately.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]
variable {X : Over (Spec (CommRingCat.of k))}

/-- A finite locally free module on a proper curve has constant rank equal to the dimension of
its fiber at the generic point. -/
instance instIsFiniteLocallyFreeOfRankFiberFinrankGenericPoint
    [Curve X] [IsProper X.hom] (ℱ : X.left.Modules) [IsFiniteLocallyFree ℱ] :
    IsFiniteLocallyFreeOfRank (fiberFinrank ℱ (genericPoint X.left)) ℱ := sorry

/-- The degree of a finite locally free module on a proper curve, with rank read from its generic
fiber. -/
noncomputable def curveDegreeOfFiniteLocallyFree
    [Curve X] [IsProper X.hom] (ℱ : X.left.Modules) [IsFiniteLocallyFree ℱ] : ℤ :=
  curveDegree X.hom (topologicalKrullDim_eq_one X).le ℱ
    (fiberFinrank ℱ (genericPoint X.left))

/-- The rank-free degree of a finite locally free module is its fixed-rank curve degree at the
generic fiber rank. -/
theorem curveDegreeOfFiniteLocallyFree_eq_curveDegree
    [Curve X] [IsProper X.hom] (ℱ : X.left.Modules) [IsFiniteLocallyFree ℱ] :
    curveDegreeOfFiniteLocallyFree ℱ =
      curveDegree X.hom (topologicalKrullDim_eq_one X).le ℱ
        (fiberFinrank ℱ (genericPoint X.left)) := sorry

end AlgebraicGeometry.Scheme.Modules
