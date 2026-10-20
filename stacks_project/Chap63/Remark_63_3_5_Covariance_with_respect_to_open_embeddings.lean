module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

universe u

/- Remark 63.3.5 (Covariance with respect to open embeddings) (1): if
`f : X ⟶ Y` is separated and locally of finite type, `F` is an abelian sheaf
on `X_étale`, and `j : X' ⟶ X` is an open immersion, there is a canonical
map `etaleLowerShriekOpenImmersion j f : f'_!(F|_{X'}) ⟶ f_! F`. -/
@[stacks 0F53]
#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekOpenImmersion :
  ∀ {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion j] [IsSeparated f] [LocallyOfFiniteType f],
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ etaleLowerShriek (j ≫ f) ⟶
      etaleLowerShriek f)

/- Remark 63.3.5 (Covariance with respect to open embeddings) (2): the
canonical comparison `f'_!(F|_{X'}) ⟶ f_! F` is injective. -/
@[stacks 0F53]
#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekOpenImmersion_app_mono :
  ∀ {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion j] [IsSeparated f] [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    Mono ((etaleLowerShriekOpenImmersion j f).app F))

/- Remark 63.3.5 (Covariance with respect to open embeddings) (3): the
comparison fills the triangle with the compact-support inclusions
`etaleLowerShriekι` and the restriction of ordinary pushforwards
`etaleAbelianPushforwardRestrict`. -/
@[stacks 0F53]
#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekOpenImmersion_ι :
  ∀ {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion j] [IsSeparated f] [LocallyOfFiniteType f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    (etaleLowerShriekOpenImmersion j f).app F ≫
        (etaleLowerShriekι f).app F ≫
          (etaleAbelianPushforwardRestrict j f).app F =
      (etaleLowerShriekι (j ≫ f)).app
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F))

/- Remark 63.3.5 (Covariance with respect to open embeddings) (4): for nested
open immersions `X'' ⟶ X' ⟶ X`, the composite of the two covariance maps is
the covariance map of the composite open immersion. -/
@[stacks 0F53]
#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekOpenImmersion_comp :
  ∀ {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion j] [IsSeparated f] [LocallyOfFiniteType f]
    {X'' : Scheme.{u}} (j' : X'' ⟶ X') [IsOpenImmersion j'],
    whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
          (etaleLowerShriekOpenImmersion j' (j ≫ f)) ≫
        etaleLowerShriekOpenImmersion j f =
      whiskerRight (etaleAbelianRestrictionSheafCompIso j j').hom
          (etaleLowerShriek (j' ≫ j ≫ f)) ≫
        whiskerLeft (etaleRestrictionSheaf (j' ≫ j) AddCommGrpCat.{u})
          (etaleLowerShriekCongr (Category.assoc j' j f).symm).hom ≫
          etaleLowerShriekOpenImmersion (j' ≫ j) f)

end
