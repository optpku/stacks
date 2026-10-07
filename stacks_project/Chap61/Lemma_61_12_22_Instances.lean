module

public import stacks_project.Chap61.Definition_61_12_8_Affine
public import stacks_project.Chap61.Lemma_61_12_20_Affine
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Subcanonicality of pro-étale sites

Reusable `Subcanonical` instances for the small affine pro-étale topology and
for chosen-presentation pro-étale topologies.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.ProEt

/-- The small affine pro-étale topology of a scheme is subcanonical. -/
@[stacks 098Z]
instance affineTopology_subcanonical (S : Scheme.{u}) :
    (affineTopology S).Subcanonical := sorry

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- The chosen big affine pro-étale topology of a scheme is subcanonical. -/
@[stacks 098Z]
instance bigAffineTopology_subcanonical (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) : (bigAffineTopology X S).Subcanonical := sorry

/-- The topology of a chosen big pro-étale presentation is subcanonical. -/
instance toGrothendieck_subcanonical (X : ChosenBigProetaleSite.{u, v}) :
    X.toGrothendieck.Subcanonical := sorry

/-- The chosen big pro-étale slice topology of a scheme is subcanonical. -/
instance bigTopology_subcanonical (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) : (bigTopology X S).Subcanonical := sorry

/-- The chosen small pro-étale topology of a scheme is subcanonical. -/
instance smallTopology_subcanonical (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) : (smallTopology X S).Subcanonical := sorry

end AlgebraicGeometry.ChosenBigProetaleSite
