module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.GenericFiber
import StacksCheckRecall

/-!
# Lemma 31.11.7

Integrality of a flat morphism from its generic fiber.

@stack 0BCM
-/

@[expose] public section

universe u

/- Lemma 31.11.7: Let `f : X ⟶ Y` be a flat morphism of schemes. If `Y` is integral and the
generic fiber of `f` is integral, then `X` is integral. -/
@[stacks 0BCM] #check
  (AlgebraicGeometry.Scheme.Hom.isIntegral_of_flat_of_genericFiber :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsIntegral Y],
      AlgebraicGeometry.IsIntegral
          (AlgebraicGeometry.Scheme.Hom.fiber f (genericPoint Y)) →
        AlgebraicGeometry.IsIntegral X)
