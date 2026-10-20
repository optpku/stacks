module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.FiniteType
import StacksCheckRecall

/-!
# Locally of finite type morphisms have locally Noetherian fibres

A morphism of algebraic spaces that is locally of finite type has locally
Noetherian fibres.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 71.4.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite type, then the fibres
of `f` are locally Noetherian. -/
@[stacks 0CUY] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyNoetherianFibers.ofLocallyOfFiniteType :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f],
      AlgebraicGeometry.AlgebraicSpace.LocallyNoetherianFibers f)
