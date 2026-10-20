module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.Integral
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.15.4: An integral morphism of algebraic spaces bijective on points
detects whether source and target are schemes. -/
@[stacks 07VV] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.iff_of_isIntegralHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f],
      Function.Bijective (Points.map f) → (IsScheme X ↔ IsScheme Y))
