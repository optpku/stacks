/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Functor

/-!
# Associated modules on small standard scheme sites

This module constructs the structure sheaf and associated-module equivalence
on the small presentation of each of the five standard scheme sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule.StandardSmall

/-- The global-functions presheaf on the small `τ`-site of `S`. -/
abbrev structurePresheaf (τ : StandardTopology) (S : Scheme.{u}) :
    (StandardTopology.Small.site τ S)ᵒᵖ ⥤ RingCat.{u} :=
  Scheme.Over.structurePresheaf (StandardTopology.Small.toOver τ S)

/-- The small standard structure presheaf is obtained from the canonical
functor to `Over S`. -/
theorem structurePresheaf_def (τ : StandardTopology) (S : Scheme.{u}) :
    structurePresheaf τ S =
      Scheme.Over.structurePresheaf (StandardTopology.Small.toOver τ S) := sorry

/-- The global-functions presheaf is a sheaf on every small standard site. -/
theorem structurePresheafIsSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Presheaf.IsSheaf (StandardTopology.Small.topology τ S)
      (structurePresheaf τ S) := sorry

/-- The structure sheaf on the small `τ`-site of `S`. -/
noncomputable def structureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Sheaf (StandardTopology.Small.topology τ S) RingCat.{u} :=
  ⟨structurePresheaf τ S, structurePresheafIsSheaf τ S⟩

/-- The underlying presheaf of the small standard structure sheaf is the
global-functions presheaf. -/
theorem structureSheaf_obj (τ : StandardTopology) (S : Scheme.{u}) :
    (structureSheaf τ S).obj = structurePresheaf τ S := sorry

/-- Pullback sections of a quasi-coherent module form a sheaf on every small
standard site. -/
theorem modulePresheafIsSheaf (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (StandardTopology.Small.topology τ S)
      (Scheme.Modules.pullbackSectionsPresheaf
        (StandardTopology.Small.toOver τ S) F).presheaf := sorry

/-- The module sheaf on the small `τ`-site associated to `F`. -/
noncomputable def module (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] : SheafOfModules (structureSheaf τ S) :=
  ⟨Scheme.Modules.pullbackSectionsPresheaf
      (StandardTopology.Small.toOver τ S) F,
    modulePresheafIsSheaf τ S F⟩

/-- The underlying module presheaf is the pullback-sections presheaf. -/
theorem module_val (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (module τ S F).val = Scheme.Modules.pullbackSectionsPresheaf
      (StandardTopology.Small.toOver τ S) F := sorry

/-- The associated module of a quasi-coherent module is quasi-coherent on
every small standard site. -/
theorem moduleIsQuasicoherent (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (module τ S F).IsQuasicoherent := sorry

/-- The functor sending a quasi-coherent module on `S` to its associated
quasi-coherent module on the small `τ`-site. -/
noncomputable def functor (τ : StandardTopology) (S : Scheme.{u}) :
    Scheme.QCoh S ⥤
      (SheafOfModules.isQuasicoherent (structureSheaf τ S)).FullSubcategory where
  obj F := ⟨module τ S F.obj, moduleIsQuasicoherent τ S F.obj⟩
  map {F G} φ :=
    ⟨⟨(Scheme.Modules.pullbackSectionsFunctor
      (StandardTopology.Small.toOver τ S)).map φ.hom⟩⟩
  map_id := sorry
  map_comp := sorry

/-- The underlying sheaf of `functor τ S` is the associated module. -/
theorem functor_obj (τ : StandardTopology) (S : Scheme.{u}) (F : Scheme.QCoh S) :
    ((functor τ S).obj F).obj = module τ S F.obj := sorry

/-- The underlying presheaf morphism of `functor τ S` is the canonical
pullback-sections morphism. -/
theorem functor_map (τ : StandardTopology) (S : Scheme.{u})
    {F G : Scheme.QCoh S} (φ : F ⟶ G) :
    ((functor τ S).map φ).hom.val =
      (Scheme.Modules.pullbackSectionsFunctor
        (StandardTopology.Small.toOver τ S)).map φ.hom := sorry

namespace functor

/-- The associated-module functor to every small standard site is an
equivalence. -/
instance isEquivalence (τ : StandardTopology) (S : Scheme.{u}) :
    (functor τ S).IsEquivalence := sorry

end functor

end AlgebraicGeometry.Scheme.AssociatedModule.StandardSmall
