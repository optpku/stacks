module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NoetherianAtSpecializations.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.NoetherianAtSpecializations

/- Example 35.32.2 (1): a scheme morphism has the property when every target point
specializing from an image point has a Noetherian stalk. -/
@[stacks 04QY] #check
  (AlgebraicGeometry.NoetherianAtSpecializations.iff :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      NoetherianAtSpecializations f ↔
        ∀ (x : X) (y : Y), f x ⤳ y → IsNoetherianRing (Y.presheaf.stalk y))

/- Example 35.32.2 (2): `NoetherianAtSpecializations` is étale local on the target. -/
@[stacks 04QY] #check
  (AlgebraicGeometry.NoetherianAtSpecializations.instIsLocalAtTargetEtale :
    NoetherianAtSpecializations.IsLocalAtTarget Scheme.etalePrecoverage)

/- Example 35.32.2 (3): `NoetherianAtSpecializations` is étale local on the source. -/
@[stacks 04QY] #check
  (AlgebraicGeometry.NoetherianAtSpecializations.instIsLocalAtSourceEtale :
    NoetherianAtSpecializations.IsLocalAtSource Scheme.etalePrecoverage)

/- Example 35.32.2 (4): the square with top map `coprod.inl`, left map the identity,
bottom map `Counterexample.puncturedOpen.ι`, and right map `Counterexample.cover` commutes. -/
@[stacks 04QY] #check
  (AlgebraicGeometry.NoetherianAtSpecializations.Counterexample.square :
    (coprod.inl : Counterexample.puncturedOpen.toScheme ⟶
      Counterexample.puncturedOpen.toScheme ⨿
        Spec (CommRingCat.of Counterexample.CoordinateRing)) ≫ Counterexample.cover =
      𝟙 Counterexample.puncturedOpen.toScheme ≫ Counterexample.puncturedOpen.ι)

/- Example 35.32.2 (5): the right vertical map `Counterexample.cover` is surjective. -/
@[stacks 04QY] #check
  (AlgebraicGeometry.NoetherianAtSpecializations.Counterexample.instSurjectiveCover :
    Surjective Counterexample.cover)

/- Example 35.32.2 (6): the right vertical map `Counterexample.cover` is étale. -/
@[stacks 04QY] #check
  (AlgebraicGeometry.NoetherianAtSpecializations.Counterexample.instEtaleCover :
    Etale Counterexample.cover)

/- Example 35.32.2 (7): inclusion of the locally Noetherian punctured open into the first
summand has `NoetherianAtSpecializations`. -/
@[stacks 04QY] #check
  (AlgebraicGeometry.NoetherianAtSpecializations.Counterexample.top :
    NoetherianAtSpecializations
      (coprod.inl : Counterexample.puncturedOpen.toScheme ⟶
        Counterexample.puncturedOpen.toScheme ⨿
          Spec (CommRingCat.of Counterexample.CoordinateRing)))

/- Example 35.32.2 (8): the punctured-open immersion into the infinite-axis scheme does
not have `NoetherianAtSpecializations`. -/
@[stacks 04QY] #check
  (AlgebraicGeometry.NoetherianAtSpecializations.Counterexample.bottom_not :
    ¬ NoetherianAtSpecializations Counterexample.puncturedOpen.ι)

end AlgebraicGeometry.NoetherianAtSpecializations
