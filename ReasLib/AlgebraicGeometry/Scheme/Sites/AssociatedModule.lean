module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.PullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf

/-!
# Associated modules on scheme sites

This module constructs the presheaf of global sections of pullbacks of a scheme module
and bundles its standard big, small Zariski, and small étale specializations as sheaves.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Over

variable {C : Type w} [Category.{v} C] {B : Scheme.{u}}

/-- The global-functions presheaf induced by a functor to schemes over `B`. -/
abbrev structurePresheaf (p : C ⥤ CategoryTheory.Over B) : Cᵒᵖ ⥤ RingCat.{u} :=
  Scheme.Site.structurePresheaf (p ⋙ CategoryTheory.Over.forget B)

end AlgebraicGeometry.Scheme.Over

namespace AlgebraicGeometry.Scheme.Modules

variable {C : Type w} [Category.{v} C] {B : Scheme.{u}}

/-- Global sections of the pullback of `F` at an object of a category of schemes over `B`,
as a module over the ring of global functions on that object. -/
noncomputable abbrev pullbackSectionsObj
    (p : C ⥤ CategoryTheory.Over B) (F : B.Modules) (U : Cᵒᵖ) :
    ModuleCat.{u} ((Scheme.Over.structurePresheaf p).obj U) :=
  (RingedSpace.moduleGlobalSectionsFunctor
    (p.obj U.unop).left.toRingedSpace).obj ((pullback (p.obj U.unop).hom).obj F)

/-- Pullback of module sections is semilinear for pullback of global functions. -/
theorem pullbackSectionsMap_smul
    (p : C ⥤ CategoryTheory.Over B) (F : B.Modules) {U V : Cᵒᵖ} (f : U ⟶ V)
    (r : (Scheme.Over.structurePresheaf p).obj U) (s : pullbackSectionsObj p F U) :
    (PullbackSections.map F (p.map f.unop)).hom (r • s) =
      @SMul.smul ((Scheme.Over.structurePresheaf p).obj V)
        (pullbackSectionsObj p F V)
        (ModuleCat.isModule (pullbackSectionsObj p F V)).toSMul
        ((Scheme.Over.structurePresheaf p).map f r)
        ((PullbackSections.map F (p.map f.unop)).hom s) := sorry

/-- The semilinear restriction map on global sections of pullbacks. -/
noncomputable def pullbackSectionsMap
    (p : C ⥤ CategoryTheory.Over B) (F : B.Modules) {U V : Cᵒᵖ} (f : U ⟶ V) :
    pullbackSectionsObj p F U ⟶
      (ModuleCat.restrictScalars ((Scheme.Over.structurePresheaf p).map f).hom).obj
        (pullbackSectionsObj p F V) :=
  let source := pullbackSectionsObj p F U
  let target :=
    (ModuleCat.restrictScalars ((Scheme.Over.structurePresheaf p).map f).hom).obj
      (pullbackSectionsObj p F V)
  @ModuleCat.ofHom ((Scheme.Over.structurePresheaf p).obj U) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := (PullbackSections.map F (p.map f.unop)).hom
      map_add' := (PullbackSections.map F (p.map f.unop)).hom.map_add
      map_smul' := pullbackSectionsMap_smul p F f }

/-- Restriction on pullback sections along an identity is the canonical identity with
restricted scalars. -/
theorem pullbackSectionsMap_id
    (p : C ⥤ CategoryTheory.Over B) (F : B.Modules) (U : Cᵒᵖ) :
    pullbackSectionsMap p F (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((Scheme.Over.structurePresheaf p).map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom ((Scheme.Over.structurePresheaf p).map_id U))).inv.app _ := sorry

/-- Restriction maps on pullback sections respect composition. -/
theorem pullbackSectionsMap_comp
    (p : C ⥤ CategoryTheory.Over B) (F : B.Modules)
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    pullbackSectionsMap p F (f ≫ g) =
      pullbackSectionsMap p F f ≫
        (ModuleCat.restrictScalars ((Scheme.Over.structurePresheaf p).map f).hom).map
          (pullbackSectionsMap p F g) ≫
        (ModuleCat.restrictScalarsComp'
          ((Scheme.Over.structurePresheaf p).map f).hom
          ((Scheme.Over.structurePresheaf p).map g).hom
          ((Scheme.Over.structurePresheaf p).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom
            ((Scheme.Over.structurePresheaf p).map_comp f g))).inv.app _ := sorry

/-- The module presheaf sending `f : T ⟶ B` to the global sections of `f^*F`. -/
noncomputable def pullbackSectionsPresheaf
    (p : C ⥤ CategoryTheory.Over B) (F : B.Modules) :
    _root_.PresheafOfModules (Scheme.Over.structurePresheaf p) where
  obj U := pullbackSectionsObj p F U
  map f := pullbackSectionsMap p F f
  map_id U := pullbackSectionsMap_id p F U
  map_comp f g := pullbackSectionsMap_comp p F f g

/-- Objectwise, the pullback-sections presheaf is the global-sections module of the
corresponding pullback of `F`. -/
theorem pullbackSectionsPresheaf_obj
    (p : C ⥤ CategoryTheory.Over B) (F : B.Modules) (U : Cᵒᵖ) :
    (pullbackSectionsPresheaf p F).obj U = pullbackSectionsObj p F U := sorry

/-- The restriction morphism of the pullback-sections presheaf is the canonical
semilinear pullback map. -/
theorem pullbackSectionsPresheaf_map
    (p : C ⥤ CategoryTheory.Over B) (F : B.Modules) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (pullbackSectionsPresheaf p F).map f = pullbackSectionsMap p F f := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.StandardTopology.Big

/-- Pullback sections of a quasi-coherent module form a sheaf on the big standard
`τ`-site. -/
theorem pullbackSectionsPresheaf_isSheaf
    (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (τ.overTopology S)
      (Scheme.Modules.pullbackSectionsPresheaf (𝟭 (Over S)) F).presheaf := sorry

/-- The sheaf of modules on the big standard `τ`-site associated to a quasi-coherent
module on `S`. -/
noncomputable def associatedModule
    (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules (structureSheaf τ S) :=
  ⟨Scheme.Modules.pullbackSectionsPresheaf (𝟭 (Over S)) F,
    pullbackSectionsPresheaf_isSheaf τ S F⟩

/-- At `f : T ⟶ S`, the associated big-site module has value `Γ(T, f^*F)`. -/
theorem associatedModule_obj
    (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (U : Over S) :
    (associatedModule τ S F).val.obj (op U) =
      Scheme.Modules.pullbackSectionsObj (𝟭 (Over S)) F (op U) := sorry

/-- Restriction in the associated big-site module is the canonical pullback-sections map. -/
theorem associatedModule_map
    (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    {U V : Over S} (f : U ⟶ V) :
    (associatedModule τ S F).val.map f.op =
      Scheme.Modules.pullbackSectionsMap (𝟭 (Over S)) F f.op := sorry

end AlgebraicGeometry.StandardTopology.Big

namespace AlgebraicGeometry.Scheme.Zariski.Small

/-- Pullback sections of a quasi-coherent module form a sheaf on the small Zariski site. -/
theorem pullbackSectionsPresheaf_isSheaf
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf S.smallZariskiTopology
      (Scheme.Modules.pullbackSectionsPresheaf S.smallZariskiForget F).presheaf := sorry

/-- The sheaf of modules on the small Zariski site associated to a quasi-coherent module
on `S`. -/
noncomputable def associatedModule
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules (structureSheaf S) :=
  ⟨Scheme.Modules.pullbackSectionsPresheaf S.smallZariskiForget F,
    pullbackSectionsPresheaf_isSheaf S F⟩

/-- At `f : T ⟶ S`, the associated small-Zariski module has value `Γ(T, f^*F)`. -/
theorem associatedModule_obj
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] (U : S.smallZariskiSite) :
    (associatedModule S F).val.obj (op U) =
      Scheme.Modules.pullbackSectionsObj S.smallZariskiForget F (op U) := sorry

/-- Restriction in the associated small-Zariski module is the canonical
pullback-sections map. -/
theorem associatedModule_map
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    {U V : S.smallZariskiSite} (f : U ⟶ V) :
    (associatedModule S F).val.map f.op =
      Scheme.Modules.pullbackSectionsMap S.smallZariskiForget F f.op := sorry

end AlgebraicGeometry.Scheme.Zariski.Small

namespace AlgebraicGeometry.Scheme.Etale.Small

/-- Pullback sections of a quasi-coherent module form a sheaf on the small étale site. -/
theorem pullbackSectionsPresheaf_isSheaf
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf S.smallEtaleTopology
      (Scheme.Modules.pullbackSectionsPresheaf (Scheme.Etale.forget S) F).presheaf := sorry

/-- The sheaf of modules on the small étale site associated to a quasi-coherent module
on `S`. -/
noncomputable def associatedModule
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules (structureSheaf S) :=
  ⟨Scheme.Modules.pullbackSectionsPresheaf (Scheme.Etale.forget S) F,
    pullbackSectionsPresheaf_isSheaf S F⟩

/-- At `f : T ⟶ S`, the associated small-étale module has value `Γ(T, f^*F)`. -/
theorem associatedModule_obj
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] (U : S.Etale) :
    (associatedModule S F).val.obj (op U) =
      Scheme.Modules.pullbackSectionsObj (Scheme.Etale.forget S) F (op U) := sorry

/-- Restriction in the associated small-étale module is the canonical
pullback-sections map. -/
theorem associatedModule_map
    (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    {U V : S.Etale} (f : U ⟶ V) :
    (associatedModule S F).val.map f.op =
      Scheme.Modules.pullbackSectionsMap (Scheme.Etale.forget S) F f.op := sorry

end AlgebraicGeometry.Scheme.Etale.Small
