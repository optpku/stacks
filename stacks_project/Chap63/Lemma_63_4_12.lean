/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.GeneralComposition
import StacksCheckRecall

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.GeometricPoint AlgebraicGeometry.Scheme.Etale

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [HasCoproducts.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/- Lemma 63.4.12. Compact-support direct image along composable locally
quasi-finite morphisms has a canonical composition isomorphism. Its five
compatibilities are separated composition, mixed composition, geometric stalks,
associativity, and pasted cartesian base change. -/
@[stacks 0F6T] #check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorCompIso f g :
    lowerShriek (f ≫ g) ≅ lowerShriek f ⋙ lowerShriek g)

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorCompIso_app f g :
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      (lowerShriek (f ≫ g)).obj F ≅
      (lowerShriek g).obj ((lowerShriek f).obj F))

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorCompIso_hom f g :
    (lowerShriekFunctorCompIso f g).hom = lowerShriekFunctorComp f g)

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorCompIso_inv f g :
    (lowerShriekFunctorCompIso f g).inv = lowerShriekFunctorCompInv f g)

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorComp_app_eq f g :
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      (lowerShriekFunctorComp f g).app F = lowerShriekFunctorComp_app f g F)

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorCompInv_app_eq f g :
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      (lowerShriekFunctorCompInv f g).app F =
      lowerShriekFunctorCompInv_app f g F)

section separated

variable [IsSeparated f] [IsSeparated g]

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorCompIso_separated f g :
    ((lowerShriekIso_separated (f ≫ g)).hom ≫ (etaleLowerShriekCompIso f g).inv) =
      ((lowerShriekFunctorCompIso f g).hom ≫
    whiskerRight (lowerShriekIso_separated f).hom (lowerShriek g) ≫
    whiskerLeft (etaleLowerShriek f) (lowerShriekIso_separated g).hom))

end separated

section mixed

variable [IsSeparated g]

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorCompIso_mixed f g :
    ((lowerShriekFunctorCompIso f g).hom ≫
    whiskerLeft (lowerShriek f) (lowerShriekIso_separated g).hom) =
      (lowerShriekComp f g))

end mixed

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorCompIso_stalk f g :
    ∀ (zbar : GeometricPoint Z)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      CommSq (((lowerShriekStalkIso (f ≫ g) zbar).app F).hom)
      ((toSmallEtalePoint zbar).sheafFiber.map
        ((lowerShriekFunctorCompIso f g).hom.app F))
      (𝟙 ((abelianStalkCoproduct (f ≫ g) zbar).obj F))
      (((lowerShriekStalkIso g zbar).app ((lowerShriek f).obj F)).hom ≫
    (abelianStalkCoproductCompIso f g zbar).hom.app F))

section assoc

variable {T : Scheme.{u}} (h : Z ⟶ T)
variable [LocallyQuasiFinite h] [LocallyOfFiniteType h]
variable [HasCoproducts.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorCompIso_assoc f g h :
    ((lowerShriekFunctorCompIso (f ≫ g) h).hom ≫
    whiskerRight ((lowerShriekFunctorCompIso f g).hom) (lowerShriek h) ≫
    (associator (lowerShriek f) (lowerShriek g) (lowerShriek h)).hom) =
      (lowerShriekCongr (Category.assoc f g h)).hom ≫
        ((lowerShriekFunctorCompIso f (g ≫ h)).hom ≫
    whiskerLeft (lowerShriek f) ((lowerShriekFunctorCompIso g h).hom)))

end assoc

section baseChange

variable {X' Y' Z' : Scheme.{u}}
variable (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X)
variable (h_upper : IsPullback c f' f b) (h_lower : IsPullback b g' g a)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [LocallyQuasiFinite g'] [LocallyOfFiniteType g']
variable [HasCoproducts.{u} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u})]

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekFunctorCompIso_baseChange f g f' g' a b c h_upper h_lower :
    (whiskerRight ((lowerShriekFunctorCompIso f g).hom) (etaleAbelianSheafPullback a) ≫
    (associator (lowerShriek f) (lowerShriek g) (etaleAbelianSheafPullback a)).hom ≫
    whiskerLeft (lowerShriek f) (lowerShriekBaseChange g a g' b h_lower) ≫
    (associator (lowerShriek f) (etaleAbelianSheafPullback b) (lowerShriek g')).inv ≫
    whiskerRight (lowerShriekBaseChange f b f' c h_upper) (lowerShriek g') ≫
    (associator (etaleAbelianSheafPullback c) (lowerShriek f') (lowerShriek g')).hom) =
      (lowerShriekBaseChange (f ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) ≫
    whiskerLeft (etaleAbelianSheafPullback c) ((lowerShriekFunctorCompIso f' g').hom)))

end baseChange

variable (zbar : GeometricPoint Z)

#check (AlgebraicGeometry.Scheme.Etale.abelianStalkCoproductCompIso_hom f g zbar :
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      (abelianStalkCoproductCompIso f g zbar).hom.app F =
      Sigma.desc fun y : Fiber g zbar ↦
        ((lowerShriekStalkIso f y.point).app F).hom ≫
          Sigma.desc fun x : Fiber f y.point ↦
            Sigma.ι
              (fun w : Fiber (f ≫ g) zbar ↦
                (toSmallEtalePoint w.point).sheafFiber.obj F)
              ((Fiber.compEquiv f g zbar).symm ⟨y, x⟩))

section
variable (x : Fiber (f ≫ g) zbar)

#check (AlgebraicGeometry.Scheme.GeometricPoint.Fiber.compEquiv_fst f g zbar x :
  (Fiber.compEquiv f g zbar x).1.lift = x.lift ≫ f)

#check (AlgebraicGeometry.Scheme.GeometricPoint.Fiber.compEquiv_snd f g zbar x :
  (Fiber.compEquiv f g zbar x).2.lift = x.lift)

#check (AlgebraicGeometry.Scheme.GeometricPoint.Fiber.compEquiv_point f g zbar x :
  (Fiber.compEquiv f g zbar x).2.point = x.point)

end
