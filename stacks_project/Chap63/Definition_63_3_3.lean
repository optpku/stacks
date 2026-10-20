module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 63.3.3: if `f : X ⟶ Y` is a separated, locally of finite type
morphism of schemes and `F` is an abelian sheaf on `X_étale`, the Lemma 63.3.1
subsheaf of `f_* F` consisting of sections whose étale support is proper over
the base is named `etaleLowerShriek f`, the direct image with compact support.
The inclusion `etaleLowerShriekι` realizes
`etaleLowerShriek f ⟶ (smallEtalePullback f).sheafPushforwardContinuous
  AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology`. -/
@[stacks 0F4Z] #check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriek :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.IsSeparated f],
    CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

end
