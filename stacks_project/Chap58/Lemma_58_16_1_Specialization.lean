/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiberMap
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Specialization

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

universe u w

#check (AlgebraicGeometry.Scheme.Hom.geometricFiberMap :
  ∀ {Y X T S : Scheme.{u}} (i : Y ⟶ X) (g : Y ⟶ T)
    (f : X ⟶ S) (k : T ⟶ S) (sq : CommSq i g f k)
    (tbar : Scheme.GeometricPoint T),
    pullback g tbar.hom ⟶ pullback f (tbar.map k).hom)

#check (EtaleFundamentalGroup.IsSpecializationMap.iff_exists :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F)),
    EtaleFundamentalGroup.IsSpecializationMap f sbar' sbar hSpec F' F sp ↔
      Specializes sbar'.image sbar.image ∧ ∃ (Rsh : Type u) (_ : CommRing Rsh)
          (_ : Algebra (S.presheaf.stalk sbar.image) Rsh)
          (_ : IsStrictHenselizationOf (S.presheaf.stalk sbar.image) Rsh),
        ∃ (generalLift : Spec (.of sbar'.K) ⟶ Scheme.strictHenselizationScheme S sbar Rsh)
          (specialLift : Spec (.of sbar.K) ⟶ Scheme.strictHenselizationScheme S sbar Rsh),
          generalLift ≫ Scheme.strictHenselizationMap S sbar Rsh = sbar'.hom ∧
            specialLift ≫ Scheme.strictHenselizationMap S sbar Rsh = sbar.hom ∧
            Specializes (generalLift default) (specialLift default) ∧
            ∃ (generalToStrict : pullback f sbar'.hom ⟶
                  pullback f (Scheme.strictHenselizationMap S sbar Rsh))
              (specialToStrict : pullback f sbar.hom ⟶
                  pullback f (Scheme.strictHenselizationMap S sbar Rsh)),
              generalToStrict ≫ pullback.fst f (Scheme.strictHenselizationMap S sbar Rsh) =
                  pullback.fst f sbar'.hom ∧
                generalToStrict ≫ pullback.snd f (Scheme.strictHenselizationMap S sbar Rsh) =
                  pullback.snd f sbar'.hom ≫ generalLift ∧
                specialToStrict ≫ pullback.fst f (Scheme.strictHenselizationMap S sbar Rsh) =
                  pullback.fst f sbar.hom ∧
                specialToStrict ≫ pullback.snd f (Scheme.strictHenselizationMap S sbar Rsh) =
                  pullback.snd f sbar.hom ≫ specialLift ∧
                ∃ (specialEquiv :
                      Scheme.FiniteEtale (pullback f (Scheme.strictHenselizationMap S sbar Rsh)) ≌
                        Scheme.FiniteEtale (pullback f sbar.hom)),
                    specialEquiv.functor = Scheme.finiteEtaleBaseChange specialToStrict ∧
                    ∃ _ :
                        CatCommSq (specialEquiv.inverse ⋙ Scheme.finiteEtaleBaseChange generalToStrict)
                          (functorToAction F) (functorToAction F')
                          (Action.res FintypeCat sp.toMonoidHom),
                      exactFunctor (Scheme.FiniteEtale (pullback f sbar.hom))
                        (Scheme.FiniteEtale (pullback f sbar'.hom))
                        (specialEquiv.inverse ⋙ Scheme.finiteEtaleBaseChange generalToStrict))
