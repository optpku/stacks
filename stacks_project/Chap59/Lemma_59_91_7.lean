module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Surjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

/- Lemma 59.91.7: if `f : X ⟶ Y` and `g : Y ⟶ Z` are proper morphisms of schemes,
cohomology commutes with base change for `f` and for `g ∘ f` (i.e. `f ≫ g`),
and `f` is surjective, then cohomology commutes with base change for `g`. -/
@[stacks 0A4C] #check
  (AlgebraicGeometry.Scheme.Hom.cohomologyCommutesWithBaseChange_of_comp.{u} :
    ∀ {X Y Z : Scheme.{u}}
      [∀ W : Scheme.{u}, HasSheafify W.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ W : Scheme.{u},
        HasInjectiveResolutions (Sheaf W.smallEtaleTopology AddCommGrpCat.{u})]
      (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g] [Surjective f],
      CohomologyCommutesWithBaseChange f →
      CohomologyCommutesWithBaseChange (f ≫ g) →
      CohomologyCommutesWithBaseChange g)

end

end
