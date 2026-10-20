module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.WeaklyAssociatedPoints.Reduced
import StacksCheckRecall

/-!
# Lemma 71.2.12

The weakly associated points of a reduced algebraic space are exactly its
codimension-`0` points.
-/

@[expose] public section

universe u

/- Lemma 71.2.12: for a scheme `S` and a reduced algebraic space `X` over `S`,
the weakly associated points of `X` are exactly the codimension `0` points of
`X`. -/
@[stacks 0EN1] #check
  (AlgebraicGeometry.AlgebraicSpace.weakAss_eq_codimZeroPoints :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
      [AlgebraicGeometry.AlgebraicSpace.IsReduced X],
      AlgebraicGeometry.AlgebraicSpace.weakAss X =
        AlgebraicGeometry.AlgebraicSpace.codimZeroPoints X)

#check (AlgebraicGeometry.AlgebraicSpace.mem_weakAss_iff_mem_codimZeroPoints :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsReduced X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    x ∈ AlgebraicGeometry.AlgebraicSpace.weakAss X ↔
      x ∈ AlgebraicGeometry.AlgebraicSpace.codimZeroPoints X)
