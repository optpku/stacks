module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.BaseChange
public import stacks_project.Chap63.Lemma_63_4_10_Comparison

import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.Hom

universe u

/- Lemma 63.4.10. For a cartesian square with locally quasi-finite vertical
maps in the locally finite-type convention, compact-support direct image
commutes naturally with inverse image on abelian étale sheaves, compatibly
with the geometric-stalk coproduct square. -/
@[stacks 0F5J] #check (AlgebraicGeometry.Scheme.Etale.lowerShriekBaseChangeIso :
  ∀ {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    [LocallyQuasiFinite f] [LocallyQuasiFinite f']
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'],
    lowerShriek f ⋙ etaleAbelianSheafPullback g ≅
      etaleAbelianSheafPullback g' ⋙ lowerShriek f')

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekBaseChangeIso_app f g f' g' h_cart :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    (etaleAbelianSheafPullback g).obj ((lowerShriek f).obj F) ≅
      (lowerShriek f').obj ((etaleAbelianSheafPullback g').obj F))

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekBaseChangeIso_hom f g f' g' h_cart :
  (lowerShriekBaseChangeIso f g f' g' h_cart).hom =
    lowerShriekBaseChange f g f' g' h_cart)

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
