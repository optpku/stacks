/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Quasicoherent

/-!
# Associated-module functors on standard scheme sites

This module makes the associated-module constructions functorial in the
quasi-coherent module on the base scheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Modules

variable {C : Type w} [Category.{v} C] {S : Scheme.{u}}

/-- Pullback followed by global sections, functorially assembled into a module presheaf. -/
noncomputable def pullbackSectionsFunctor (p : C ⥤ Over S) :
    S.Modules ⥤ _root_.PresheafOfModules (Scheme.Over.structurePresheaf p) where
  obj F := pullbackSectionsPresheaf p F
  map {F G} φ :=
    { app := fun U ↦
        (RingedSpace.moduleGlobalSectionsFunctor
          (p.obj U.unop).left.toRingedSpace).map
            ((pullback (p.obj U.unop).hom).map φ)
      naturality := fun _ ↦ sorry }
  map_id := sorry
  map_comp := sorry

/-- The object action of `pullbackSectionsFunctor` is `pullbackSectionsPresheaf`. -/
theorem pullbackSectionsFunctor_obj (p : C ⥤ Over S) (F : S.Modules) :
    (pullbackSectionsFunctor p).obj F = pullbackSectionsPresheaf p F := sorry

/-- The component of the morphism action of `pullbackSectionsFunctor` is obtained by
pulling back the module morphism and applying global sections. -/
theorem pullbackSectionsFunctor_map_app (p : C ⥤ Over S) {F G : S.Modules}
    (φ : F ⟶ G) (U : Cᵒᵖ) :
    ((pullbackSectionsFunctor p).map φ).app U =
      (RingedSpace.moduleGlobalSectionsFunctor
        (p.obj U.unop).left.toRingedSpace).map
          ((pullback (p.obj U.unop).hom).map φ) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The functor sending a quasi-coherent module on `S` to its associated
quasi-coherent module sheaf on the big standard `τ`-site. -/
noncomputable def bigFunctor (τ : StandardTopology) (S : Scheme.{u}) :
    Scheme.QCoh S ⥤
      (SheafOfModules.isQuasicoherent (bigStructureSheaf τ S)).FullSubcategory where
  obj F :=
    ⟨big τ S F.obj,
      instIsQuasicoherentBig τ S F.obj⟩
  map {F G} φ :=
    ⟨⟨(Scheme.Modules.pullbackSectionsFunctor (Functor.id (Over S))).map φ.hom⟩⟩
  map_id := sorry
  map_comp := sorry

namespace bigFunctor

/-- The underlying sheaf of `bigFunctor τ S` at `F` is the associated big-site module. -/
theorem obj_obj (τ : StandardTopology) (S : Scheme.{u}) (F : Scheme.QCoh S) :
    ((bigFunctor τ S).obj F).obj = big τ S F.obj := sorry

/-- The underlying presheaf morphism of `bigFunctor τ S` is the canonical
pullback-sections morphism. -/
theorem map_hom (τ : StandardTopology) (S : Scheme.{u}) {F G : Scheme.QCoh S}
    (φ : F ⟶ G) :
    ((bigFunctor τ S).map φ).hom.val =
      (Scheme.Modules.pullbackSectionsFunctor (Functor.id (Over S))).map φ.hom := sorry

end bigFunctor

/-- The functor sending a quasi-coherent module on `S` to its associated
quasi-coherent module sheaf on the selected small standard site. -/
noncomputable def smallFunctor (σ : SmallStandardTopology) (S : Scheme.{u}) :
    Scheme.QCoh S ⥤
      (SheafOfModules.isQuasicoherent (smallStructureSheaf σ S)).FullSubcategory where
  obj F :=
    ⟨small σ S F.obj,
      instIsQuasicoherentSmall σ S F.obj⟩
  map {F G} φ :=
    ⟨⟨(Scheme.Modules.pullbackSectionsFunctor (σ.toOver S)).map φ.hom⟩⟩
  map_id := sorry
  map_comp := sorry

namespace smallFunctor

/-- The underlying sheaf of `smallFunctor σ S` at `F` is the associated small-site module. -/
theorem obj_obj (σ : SmallStandardTopology) (S : Scheme.{u}) (F : Scheme.QCoh S) :
    ((smallFunctor σ S).obj F).obj = small σ S F.obj := sorry

/-- The underlying presheaf morphism of `smallFunctor σ S` is the canonical
pullback-sections morphism. -/
theorem map_hom (σ : SmallStandardTopology) (S : Scheme.{u}) {F G : Scheme.QCoh S}
    (φ : F ⟶ G) :
    ((smallFunctor σ S).map φ).hom.val =
      (Scheme.Modules.pullbackSectionsFunctor (σ.toOver S)).map φ.hom := sorry

end smallFunctor

end AlgebraicGeometry.Scheme.AssociatedModule
