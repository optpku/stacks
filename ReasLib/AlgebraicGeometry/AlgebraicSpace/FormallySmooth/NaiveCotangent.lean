module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal smoothness via the naive cotangent complex

A morphism of algebraic spaces is formally smooth if and only if the degree `-1`
homology of its naive cotangent complex vanishes and its sheaf of relative
differentials is locally projective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-- A morphism of algebraic spaces over a scheme is formally smooth if and only if
the degree `-1` homology of its naive cotangent complex is zero and its sheaf of
relative differentials is locally projective. -/
@[stacks 0D10]
theorem iff_naiveCotangent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallySmooth f ↔ IsZero ((NL[f]).homology (-1)) ∧ IsLocallyProjective Ω[f] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallySmooth
