module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.OpenImmersion
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap59.Lemma_59_54_1
public import stacks_project.Chap63.Lemma_63_2_1
public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

universe u

/- Remark 63.3.5 (Covariance with respect to open embeddings): covariance of
compact-support pushforward along an open immersion of the source. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekOpenImmersion :
  ∀ {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion j] [IsSeparated f] [LocallyOfFiniteType f],
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ etaleLowerShriek (j ≫ f) ⟶
      etaleLowerShriek f)

end
