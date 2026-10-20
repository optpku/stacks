module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.SourceLocus
import StacksCheckRecall

/-!
# Unramified locus of a locally finite-type morphism of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.38.10: In a commutative triangle `X ⟶ Y ⟶ Z` of algebraic
spaces over a scheme, assume that `X ⟶ Z` is locally of finite type. The
points where `X ⟶ Y` is unramified form an open subspace of `X`, and this
open subspace commutes with every base change `Z' ⟶ Z`. -/
@[stacks 05W2]
#check (AlgebraicGeometry.AlgebraicSpace.unramified_sourceLocus_eq_preimage_of_over_baseChange :
  ∀ {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)],
    (Unramified.sourceLocus (Unramified.overBaseChange f q g)).pointsSet =
      Points.map (pullback.fst (f ≫ q) g) ⁻¹'
        (Unramified.sourceLocus f).pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.sourceLocus_pointsSet_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    (Unramified.sourceLocus f).pointsSet = {x | UnramifiedAt f x})

end AlgebraicGeometry.AlgebraicSpace
