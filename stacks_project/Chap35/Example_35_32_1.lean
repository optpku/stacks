module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianTarget.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- The relevant morphism property records exactly that its target is locally Noetherian. -/
#check
  (AlgebraicGeometry.LocallyNoetherianTarget :
    CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})

/- Source-side invariance is expressed by arbitrary precomposition. This avoids the stronger
family-based locality assertion, whose reverse implication fails for the empty étale cover of
an empty source. -/
#check
  (AlgebraicGeometry.LocallyNoetherianTarget.precomp_iff :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z),
      AlgebraicGeometry.LocallyNoetherianTarget (g ≫ f) ↔
        AlgebraicGeometry.LocallyNoetherianTarget f)

/- Having locally Noetherian target is local at the target for the étale precoverage. -/
#check
  (AlgebraicGeometry.LocallyNoetherianTarget.instIsLocalAtTargetEtale :
    CategoryTheory.MorphismProperty.IsLocalAtTarget
      (AlgebraicGeometry.LocallyNoetherianTarget :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage)

/- An étale open immersion from a locally Noetherian scheme to a non-locally-Noetherian
scheme gives an identity with the property whose composite does not have the property. -/
#check
  (AlgebraicGeometry.LocallyNoetherianTarget.existsOpenImmersionCounterexample :
    ∃ (Y Z : AlgebraicGeometry.Scheme.{0}) (g : Y ⟶ Z),
      AlgebraicGeometry.IsOpenImmersion g ∧ AlgebraicGeometry.Etale g ∧
        AlgebraicGeometry.IsLocallyNoetherian Y ∧
        ¬ AlgebraicGeometry.IsLocallyNoetherian Z ∧
        AlgebraicGeometry.LocallyNoetherianTarget (𝟙 Y) ∧
        ¬ AlgebraicGeometry.LocallyNoetherianTarget ((𝟙 Y) ≫ g))

/- Example 35.32.1: the property of having locally Noetherian target is not preserved by
étale postcomposition. -/
@[stacks 04QX] #check
  (AlgebraicGeometry.LocallyNoetherianTarget.notRespectsRightEtale :
    ¬ (AlgebraicGeometry.LocallyNoetherianTarget :
      CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{0}).RespectsRight
      (@AlgebraicGeometry.Etale :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{0}))
