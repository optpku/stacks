module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth.NaiveCotangent
import StacksCheckRecall

/-!
# Formal smoothness via the naive cotangent complex

A morphism of algebraic spaces is formally smooth if and only if the degree `-1`
homology of its naive cotangent complex vanishes and its sheaf of relative
differentials is locally projective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.21.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is formally smooth if and only if
`(NL[f]).homology (-1)` is zero and `Ω[f]` is locally projective. The source
identification of degree-zero homology with `Ω[f]` is
`AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent.homologyZeroIso`. -/
@[stacks 0D10] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallySmooth.iff_naiveCotangent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.FormallySmooth f ↔
        CategoryTheory.Limits.IsZero ((NL[f]).homology (-1)) ∧
          AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective Ω[f])
