module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.BaseChange
public import stacks_project.Chap59.Proposition_59_55_2_Over
public import stacks_project.Chap63.Remark_63_4_9_Stalk

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.Hom

universe u

/- The canonical finite-support comparison and its stalk square. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekBaseChange :
  ∀ {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    [LocallyQuasiFinite f] [LocallyQuasiFinite f'],
    lowerShriek f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ lowerShriek f')

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekBaseChangeIso_stalk f g f' g' h_cart :
  ∀ (ybar' : GeometricPoint Y') (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    CommSq
      ((pullbackSheafFiberIso g ybar' ((lowerShriek f).obj F)).inv ≫
        ((lowerShriekStalkIso f (ybar'.map g)).app F).hom)
      ((toSmallEtalePoint ybar').sheafFiber.map
        (lowerShriekBaseChange_app f g f' g' h_cart F))
      ((abelianStalkCoproductBaseChangeIso f g f' g' h_cart ybar').app F).hom
      ((lowerShriekStalkIso f' ybar').app
        ((etaleAbelianSheafPullback g').obj F)).hom)
