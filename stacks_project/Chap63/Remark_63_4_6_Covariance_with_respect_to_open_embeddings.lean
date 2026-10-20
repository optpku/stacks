/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.OpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.GeometricPoint

universe u

variable {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y)
variable [IsOpenImmersion j] [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ybar : GeometricPoint Y)

/- Remark 63.4.6 (Covariance with respect to open embeddings).
For a locally quasi-finite morphism and an open immersion of its source,
sheafification of finite-support covariance gives the canonical map of lower shriek. -/
@[stacks 0F6S]
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekOpenImmersion j f :
  etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ lowerShriek (j ≫ f) ⟶
    lowerShriek f)

/- Inclusion of supports defines the presheaf covariance. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekPresheafOpenImmersion j f :
  etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ lowerShriekPresheaf (j ≫ f) ⟶
    lowerShriekPresheaf f)

/- The sheaf map is precisely the sheafification of the presheaf map. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekOpenImmersion_eq j f :
  lowerShriekOpenImmersion j f =
      whiskerRight (lowerShriekPresheafOpenImmersion j f)
        (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}))

variable (V : Y.Etale)
variable (s : FiniteSupportFormalSum (j ≫ f)
  ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V)

/- The presheaf map sends each formal sum to the same sum on the larger scheme. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekPresheafOpenImmersion_ofFormalSum j f F V s :
  ((lowerShriekPresheafOpenImmersion j f).app F).app (op V)
        (FiniteSupport.ofFormalSum (j ≫ f)
          ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V s) =
      FiniteSupport.ofFormalSum f F V
        (FreeAbelianGroup.map (FiniteSupportTerm.openImmersion j f) s))

/- Both covariance maps commute with the canonical descriptions of stalks. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekPresheafOpenImmersion_stalk j f ybar F :
  CommSq
      ((toSmallEtalePoint ybar).presheafFiber.map
        ((lowerShriekPresheafOpenImmersion j f).app F))
      ((lowerShriekPresheafStalkIso (j ≫ f) ybar).hom.app
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F))
      ((lowerShriekPresheafStalkIso f ybar).hom.app F)
      ((abelianStalkCoproductOpenImmersion j f ybar).app F))

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekOpenImmersion_stalk j f ybar F :
  CommSq
      ((toSmallEtalePoint ybar).sheafFiber.map
        ((lowerShriekOpenImmersion j f).app F))
      ((lowerShriekStalkIso (j ≫ f) ybar).hom.app
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F))
      ((lowerShriekStalkIso f ybar).hom.app F)
      ((abelianStalkCoproductOpenImmersion j f ybar).app F))

variable {X'' : Scheme.{u}} (j' : X'' ⟶ X') [IsOpenImmersion j']

/- Presheaf and sheaf covariance compose for nested open immersions. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekPresheafOpenImmersion_comp j f j' :
  whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
          (lowerShriekPresheafOpenImmersion j' (j ≫ f)) ≫
        lowerShriekPresheafOpenImmersion j f =
      whiskerRight (etaleAbelianRestrictionSheafCompIso j j').hom
          (lowerShriekPresheaf (j' ≫ j ≫ f)) ≫
        whiskerLeft (etaleRestrictionSheaf (j' ≫ j) AddCommGrpCat.{u})
          (lowerShriekPresheafCongr (Category.assoc j' j f).symm).hom ≫
          lowerShriekPresheafOpenImmersion (j' ≫ j) f)

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekOpenImmersion_comp j f j' :
  whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
          (lowerShriekOpenImmersion j' (j ≫ f)) ≫
        lowerShriekOpenImmersion j f =
      whiskerRight (etaleAbelianRestrictionSheafCompIso j j').hom
          (lowerShriek (j' ≫ j ≫ f)) ≫
        whiskerLeft (etaleRestrictionSheaf (j' ≫ j) AddCommGrpCat.{u})
          (lowerShriekCongr (Category.assoc j' j f).symm).hom ≫
          lowerShriekOpenImmersion (j' ≫ j) f)

/- The sheaf covariance is injective. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekOpenImmersion_app_mono j f F :
  Mono ((lowerShriekOpenImmersion j f).app F))

variable [IsSeparated f]

/- In the separated case, covariance agrees with compact-support covariance. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekPresheafOpenImmersion_separated j f :
  CommSq (lowerShriekPresheafOpenImmersion j f)
      (whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
        (lowerShriekPresheafComparison (j ≫ f)))
      (lowerShriekPresheafComparison f)
      (whiskerRight (etaleLowerShriekOpenImmersion j f)
        (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u})))

end
