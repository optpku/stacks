/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Functor

/-!
# Associated-module functors on standard scheme sites

This source-facing module checks the reusable associated-module functor API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Modules

variable {C : Type w} [Category.{v} C] {S : Scheme.{u}}

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsFunctor :
  (p : C ⥤ Over S) →
    S.Modules ⥤ _root_.PresheafOfModules (Scheme.Over.structurePresheaf p))

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsFunctor_obj :
  ∀ (p : C ⥤ Over S) (F : S.Modules),
    (pullbackSectionsFunctor p).obj F = pullbackSectionsPresheaf p F)

#check (AlgebraicGeometry.Scheme.Modules.pullbackSectionsFunctor_map_app :
  ∀ (p : C ⥤ Over S) {F G : S.Modules} (φ : F ⟶ G) (U : Cᵒᵖ),
    ((pullbackSectionsFunctor p).map φ).app U =
      (RingedSpace.moduleGlobalSectionsFunctor
        (p.obj U.unop).left.toRingedSpace).map
          ((pullback (p.obj U.unop).hom).map φ))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.AssociatedModule

#check (AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor :
  (τ : StandardTopology) → (S : Scheme.{u}) →
    Scheme.QCoh S ⥤
      (SheafOfModules.isQuasicoherent (bigStructureSheaf τ S)).FullSubcategory)

#check (AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor.obj_obj :
  ∀ (τ : StandardTopology) (S : Scheme.{u}) (F : Scheme.QCoh S),
    ((bigFunctor τ S).obj F).obj = big τ S F.obj)

#check (AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor.map_hom :
  ∀ (τ : StandardTopology) (S : Scheme.{u}) {F G : Scheme.QCoh S} (φ : F ⟶ G),
    ((bigFunctor τ S).map φ).hom.val =
      (Scheme.Modules.pullbackSectionsFunctor (Functor.id (Over S))).map φ.hom)

#check (AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor :
  (σ : SmallStandardTopology) → (S : Scheme.{u}) →
    Scheme.QCoh S ⥤
      (SheafOfModules.isQuasicoherent (smallStructureSheaf σ S)).FullSubcategory)

#check (AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor.obj_obj :
  ∀ (σ : SmallStandardTopology) (S : Scheme.{u}) (F : Scheme.QCoh S),
    ((smallFunctor σ S).obj F).obj = small σ S F.obj)

#check (AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor.map_hom :
  ∀ (σ : SmallStandardTopology) (S : Scheme.{u}) {F G : Scheme.QCoh S} (φ : F ⟶ G),
    ((smallFunctor σ S).map φ).hom.val =
      (Scheme.Modules.pullbackSectionsFunctor (σ.toOver S)).map φ.hom)

end AlgebraicGeometry.Scheme.AssociatedModule
