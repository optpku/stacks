/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.CategoryTheory.Pro.Presentation

/-!
# Pro-realization of coherent formal modules

This file constructs the stagewise quasicoherent diagram underlying a coherent formal module and
its associated pro-object.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical functor that regards a coherent module on a Noetherian scheme as a
quasicoherent module. -/
noncomputable def coherentToQCoh (X : Scheme.{u}) [IsNoetherian X] :
    RingedSpace.Coh X.toRingedSpace ⥤ QCoh X :=
  ObjectProperty.ιOfLE fun F hF ↦
    (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType F).mp hF |>.1

/-- The underlying module of a coherent module is unchanged by `coherentToQCoh`. -/
theorem coherentToQCoh_obj (X : Scheme.{u}) [IsNoetherian X]
    (F : RingedSpace.Coh X.toRingedSpace) :
    ((coherentToQCoh X).obj F).obj = F.obj := sorry

/-- The underlying morphism of a coherent-module map is unchanged by `coherentToQCoh`. -/
theorem coherentToQCoh_map (X : Scheme.{u}) [IsNoetherian X]
    {F G : RingedSpace.Coh X.toRingedSpace} (f : F ⟶ G) :
    ((coherentToQCoh X).map f).hom = f.hom := sorry

namespace CoherentFormalModules

/-- The functor realizing a coherent formal module as the pro-object represented by its
sequential diagram of quasicoherent stages. -/
noncomputable def proFunctor {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : CoherentFormalModules X I ⥤ Pro (QCoh X) :=
  (IsCoherentFormalModuleSystem I).ι ⋙
    (Functor.whiskeringRight ℕᵒᵖ
      (RingedSpace.Coh X.toRingedSpace) (QCoh X)).obj (coherentToQCoh X) ⋙
    Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ

/-- The pro-object underlying `proFunctor I` is represented by the stagewise quasicoherent
diagram of the given coherent formal module. -/
theorem proFunctor_obj {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModules X I) :
    (proFunctor I).obj F =
      (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj (F.obj ⋙ coherentToQCoh X) := sorry

/-- On morphisms, `proFunctor I` applies `Pro.lim` to the stagewise quasicoherent natural
transformation. -/
theorem proFunctor_map {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {F G : CoherentFormalModules X I} (f : F ⟶ G) :
    (proFunctor I).map f =
      (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).map
        (Functor.whiskerRight f.hom (coherentToQCoh X)) := sorry

/-- The functor from coherent formal modules to pro-quasicoherent modules induces a bijection
on every morphism set. -/
theorem proFunctor_map_bijective {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F G : CoherentFormalModules X I) :
    Function.Bijective (fun f : F ⟶ G ↦ (proFunctor I).map f) := sorry

/-- The pro-realization functor on coherent formal modules is full. -/
instance proFunctorFull {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : (proFunctor I).Full := sorry

/-- The pro-realization functor on coherent formal modules is faithful. -/
instance proFunctorFaithful {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : (proFunctor I).Faithful := sorry

end CoherentFormalModules

end AlgebraicGeometry.Scheme
