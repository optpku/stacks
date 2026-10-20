module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

/- Lemma 59.91.8: if `f : X ⟶ Y` and `g : Y ⟶ Z` are proper morphisms of schemes
and cohomology commutes with base change for each of `f` and `g`, then cohomology
commutes with base change for the composite `g ∘ f`, written `f ≫ g` in Lean. -/
@[stacks 0A4D] #check
  (AlgebraicGeometry.Scheme.Hom.cohomologyCommutesWithBaseChange_comp.{u} :
    ∀ {X Y Z : Scheme.{u}}
      [∀ W : Scheme.{u}, HasSheafify W.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ W : Scheme.{u},
        HasInjectiveResolutions (Sheaf W.smallEtaleTopology AddCommGrpCat.{u})]
      (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g],
      CohomologyCommutesWithBaseChange f →
      CohomologyCommutesWithBaseChange g →
      CohomologyCommutesWithBaseChange (f ≫ g))

end

end
