module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Cech

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open TopologicalSpace

universe u

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekCechAugmentedComplexFunctor :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    {ι : Type u} (𝒰 : ι → X.Opens),
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      ChainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ℕ)
