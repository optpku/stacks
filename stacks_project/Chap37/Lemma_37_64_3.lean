module

import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Diagonal
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.64.3: if the diagonal of `f : X ⟶ Y` is flat, then every
`𝒪_X`-module flat over `Y` is intrinsically flat over `X`. -/
@[stacks 094R] #check
  (AlgebraicGeometry.Scheme.Modules.IsFlat.of_flatOver_of_flat_diagonal :
    {X Y : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ Y) → (ℱ : X.Modules) →
      [AlgebraicGeometry.Flat (pullback.diagonal f)] →
      AlgebraicGeometry.Scheme.Modules.flatOver ℱ f → ℱ.IsFlat)
