/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.NaiveCotangent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormallyEtale

/-- A scheme morphism is formally étale exactly when the degree `-1` and degree `0`
homology objects of its naive cotangent complex are zero. -/
theorem iff_naiveCotangent {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FormallyEtale f ↔
      IsZero ((NL[f.toShHom]).homology (-1)) ∧
        IsZero ((NL[f.toShHom]).homology 0) := sorry

end AlgebraicGeometry.FormallyEtale
