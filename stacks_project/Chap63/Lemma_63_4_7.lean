module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Cech
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open TopologicalSpace

universe u

/- Lemma 63.4.7: The augmented Čech complex of lower shrieks for an open
covering is exact, functorially in the abelian étale sheaf. -/
@[stacks 0F5H] #check (AlgebraicGeometry.Scheme.Etale.lowerShriekCechAugmentedComplex_acyclic :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    {ι : Type u} (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    (lowerShriekCechAugmentedComplex f 𝒰 F).Acyclic)
