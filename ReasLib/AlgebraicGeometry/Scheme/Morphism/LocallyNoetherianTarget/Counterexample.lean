module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyNoetherianTarget
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NoetherianAtSpecializations.Counterexample

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.LocallyNoetherianTarget

/-- There is an étale open immersion from a locally Noetherian scheme into a scheme that is
not locally Noetherian, so its locally Noetherian identity has a composite without locally
Noetherian target. -/
theorem existsOpenImmersionCounterexample :
    ∃ (Y Z : Scheme.{0}) (g : Y ⟶ Z),
      IsOpenImmersion g ∧ Etale g ∧ IsLocallyNoetherian Y ∧ ¬ IsLocallyNoetherian Z ∧
        LocallyNoetherianTarget (𝟙 Y) ∧ ¬ LocallyNoetherianTarget ((𝟙 Y) ≫ g) := sorry

/-- The property of having locally Noetherian target is not preserved by postcomposition
with étale morphisms. -/
theorem notRespectsRightEtale :
    ¬ (LocallyNoetherianTarget : MorphismProperty Scheme.{0}).RespectsRight
      (@Etale : MorphismProperty Scheme.{0}) := sorry

end AlgebraicGeometry.LocallyNoetherianTarget
