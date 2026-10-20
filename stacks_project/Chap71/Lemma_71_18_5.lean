module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Pushforward
import StacksCheckRecall

/-!
# Affine pushforward of strict transforms of modules on algebraic spaces

Pushforward along the base change of an affine morphism of algebraic spaces
carries the strict transform of a quasi-coherent module to the strict
transform of its pushforward.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.18.5: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `Z ⊂ B` be a closed subspace. Let `b : B' ⟶ B` be the blowing up of `Z`
in `B`. Let `g : X ⟶ Y` be an affine morphism of spaces over `B`. Let `F` be
a quasi-coherent sheaf on `X`. Let `g' : X ×_B B' ⟶ Y ×_B B'` be the base
change of `g`. Let `F'` be the strict transform of `F` relative to `b`. Then
`g'_* F'` is the strict transform of `g_* F`. -/
@[stacks 0866] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward_strictTransformModule_isomorphic_of_affine :
    ∀ {S : Scheme.{u}} {B B' X Y : AlgebraicSpace S}
      (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
      (g : X ⟶ Y) (y : Y ⟶ B) [Affine g]
      (F : X.Modules) [F.IsQuasicoherent],
      IsIsomorphic
        ((Modules.pushforward (AlgebraicGeometry.AlgebraicSpace.overBaseChange g y b)).obj
          (strictTransformModule b (Z.inverseImageSubspace b) (g ≫ y) F))
        (strictTransformModule b (Z.inverseImageSubspace b) y
          ((Modules.pushforward g).obj F)))
