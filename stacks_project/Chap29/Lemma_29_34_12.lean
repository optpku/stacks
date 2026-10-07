module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials
import StacksCheckRecall

/-!
# Lemma 29.34.12

The relative differentials of a smooth morphism are finite locally free, with rank equal to the
fiber dimension at every point.

@stack 02G1
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 29.34.12: the relative differentials of a smooth morphism are finite locally free. -/
@[stacks 02G1] #check
  (AlgebraicGeometry.Smooth.differentials_isFiniteLocallyFree :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S), Smooth f →
      (Ω[f.toShHom]).IsFiniteLocallyFree)

#check
  (AlgebraicGeometry.Smooth.rankAtClosedPoint_differentials_eq_fiberDimensionAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S), Smooth f → ∀ x : X,
      (Module.rankAtStalk
        (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)
        (IsLocalRing.closedPoint (X.presheaf.stalk x)) : WithBot ℕ∞) =
        f.fiberDimensionAt x)

end AlgebraicGeometry
