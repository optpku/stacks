module

public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.StandardSmall

/-!
# Commutative structure sheaves for associated modules

This module retains the commutative-ring structure of the global-functions
presheaves used by standard-site associated-module constructions. The
coefficient rings and modules are universe-lifted so that categorical flatness
is available on the large standard sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Over

variable {C : Type w} [Category.{v} C] {S : Scheme.{u}}

/-- The universe-lifted commutative-ring-valued global-functions presheaf
attached to a functor from a site to schemes over `S`. -/
def commStructurePresheaf (p : C ⥤ Over S) : Cᵒᵖ ⥤ CommRingCat.{u + 1} :=
  p.op ⋙ (Over.forget S).op ⋙ Scheme.Γ ⋙ CommRingCat.universeLift.{u, u + 1}

/-- Objectwise, `commStructurePresheaf p` is the universe lift of the
global-sections ring in the existing structure presheaf. -/
theorem commStructurePresheaf_obj (p : C ⥤ Over S) (U : Cᵒᵖ) :
    (commStructurePresheaf p).obj U =
      CommRingCat.of
        (ULift.{u + 1, u} ((p.op ⋙ (Over.forget S).op ⋙ Scheme.Γ).obj U)) := sorry

end AlgebraicGeometry.Scheme.Over

namespace AlgebraicGeometry.Scheme.Modules

variable {C : Type w} [Category.{v} C] {S : Scheme.{u}}

/-- The universe lift of the pullback-sections module at an object of a site
over `S`. -/
noncomputable def commPullbackSectionsObj
    (p : C ⥤ Over S) (F : S.Modules) (U : Cᵒᵖ) :
    ModuleCat.{u + 1} ((Scheme.Over.commStructurePresheaf p).obj U) :=
  (ModuleCat.restrictScalars ULift.ringEquiv.toRingHom).obj
    ((ModuleCat.uliftFunctor.{u + 1, u}
      ((Scheme.Over.structurePresheaf p).obj U)).obj (pullbackSectionsObj p F U))

/-- The underlying type of `commPullbackSectionsObj p F U` is the universe
lift of the ordinary pullback-sections module. -/
theorem commPullbackSectionsObj_carrier
    (p : C ⥤ Over S) (F : S.Modules) (U : Cᵒᵖ) :
    commPullbackSectionsObj p F U =
      (ModuleCat.restrictScalars ULift.ringEquiv.toRingHom).obj
        ((ModuleCat.uliftFunctor.{u + 1, u}
          ((Scheme.Over.structurePresheaf p).obj U)).obj
            (pullbackSectionsObj p F U)) := sorry

/-- The target module for a lifted pullback-section restriction map. -/
noncomputable abbrev commPullbackSectionsTarget
    (p : C ⥤ Over S) (F : S.Modules) {U V : Cᵒᵖ} (f : U ⟶ V) :=
  (ModuleCat.restrictScalars
    ((Scheme.Over.commStructurePresheaf p).map f).hom).obj
      (commPullbackSectionsObj p F V)

/-- The target of a lifted restriction map is obtained by restricting scalars
along the lifted map of coefficient rings. -/
theorem commPullbackSectionsTarget_def
    (p : C ⥤ Over S) (F : S.Modules) {U V : Cᵒᵖ} (f : U ⟶ V) :
    commPullbackSectionsTarget p F f =
      (ModuleCat.restrictScalars
        ((Scheme.Over.commStructurePresheaf p).map f).hom).obj
          (commPullbackSectionsObj p F V) := sorry

/-- The lifted pullback-section map preserves addition. -/
theorem commPullbackSectionsMap_add
    (p : C ⥤ Over S) (F : S.Modules) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x y : commPullbackSectionsObj p F U) :
    ULift.up (pullbackSectionsMap p F f ((x + y).down)) =
      ULift.up (pullbackSectionsMap p F f x.down) +
        ULift.up (pullbackSectionsMap p F f y.down) := sorry

/-- The lifted pullback-section map is linear for the lifted restriction map
on the coefficient rings. -/
theorem commPullbackSectionsMap_smul
    (p : C ⥤ Over S) (F : S.Modules) {U V : Cᵒᵖ} (f : U ⟶ V)
    (r : (Scheme.Over.commStructurePresheaf p).obj U)
    (x : commPullbackSectionsObj p F U) :
    (ULift.up (pullbackSectionsMap p F f ((r • x).down)) :
      commPullbackSectionsTarget p F f) =
      @SMul.smul ((Scheme.Over.commStructurePresheaf p).obj U)
        (commPullbackSectionsTarget p F f)
        (ModuleCat.isModule (commPullbackSectionsTarget p F f)).toSMul r
        (ULift.up (pullbackSectionsMap p F f x.down)) := sorry

/-- The universe lift of the restriction map on pullback sections. -/
noncomputable def commPullbackSectionsMap
    (p : C ⥤ Over S) (F : S.Modules) {U V : Cᵒᵖ} (f : U ⟶ V) :
    commPullbackSectionsObj p F U ⟶ commPullbackSectionsTarget p F f :=
  ModuleCat.ofHom (X := commPullbackSectionsObj p F U)
    (Y := commPullbackSectionsTarget p F f)
    { toFun := fun x ↦ ULift.up (pullbackSectionsMap p F f x.down)
      map_add' := commPullbackSectionsMap_add p F f
      map_smul' := commPullbackSectionsMap_smul p F f }

/-- The lifted restriction map is obtained by applying module universe lift
and then restricting scalars along `ULift.ringEquiv`. -/
theorem commPullbackSectionsMap_apply
    (p : C ⥤ Over S) (F : S.Modules) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ∀ x : commPullbackSectionsObj p F U,
      commPullbackSectionsMap p F f x =
        (ULift.up (pullbackSectionsMap p F f x.down) :
          commPullbackSectionsTarget p F f) := sorry

/-- Lifted pullback-section restriction maps respect identity morphisms. -/
theorem commPullbackSectionsMap_id
    (p : C ⥤ Over S) (F : S.Modules) (U : Cᵒᵖ) :
    commPullbackSectionsMap p F (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        ((Scheme.Over.commStructurePresheaf p).map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom
          ((Scheme.Over.commStructurePresheaf p).map_id U))).inv.app _ := sorry

/-- Lifted pullback-section restriction maps respect composition. -/
theorem commPullbackSectionsMap_comp
    (p : C ⥤ Over S) (F : S.Modules)
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    commPullbackSectionsMap p F (f ≫ g) =
      commPullbackSectionsMap p F f ≫
        (ModuleCat.restrictScalars
          ((Scheme.Over.commStructurePresheaf p).map f).hom).map
            (commPullbackSectionsMap p F g) ≫
        (ModuleCat.restrictScalarsComp'
          ((Scheme.Over.commStructurePresheaf p).map f).hom
          ((Scheme.Over.commStructurePresheaf p).map g).hom
          ((Scheme.Over.commStructurePresheaf p).map (f ≫ g)).hom
          (congrArg CommRingCat.Hom.hom
            ((Scheme.Over.commStructurePresheaf p).map_comp f g))).inv.app _ := sorry

/-- The universe-lifted pullback-sections presheaf over the commutative
global-functions presheaf. -/
noncomputable def commPullbackSectionsPresheaf
    (p : C ⥤ Over S) (F : S.Modules) :
    _root_.PresheafOfModules.{u + 1}
      (CategoryTheory.Presheaf.ringPresheafOfComm
        (Scheme.Over.commStructurePresheaf p)) where
  obj U := commPullbackSectionsObj p F U
  map f := commPullbackSectionsMap p F f
  map_id U := commPullbackSectionsMap_id p F U
  map_comp f g := commPullbackSectionsMap_comp p F f g

/-- Objectwise, `commPullbackSectionsPresheaf p F` is the universe lift of the
ordinary pullback-sections module. -/
theorem commPullbackSectionsPresheaf_obj
    (p : C ⥤ Over S) (F : S.Modules) (U : Cᵒᵖ) :
    (commPullbackSectionsPresheaf p F).obj U =
      commPullbackSectionsObj p F U := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The lifted commutative global-functions presheaf is a sheaf on a standard
big site. -/
theorem bigCommStructurePresheaf_isSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Presheaf.IsSheaf (τ.overTopology S)
      (Scheme.Over.commStructurePresheaf (Functor.id (Over S))) := sorry

/-- The lifted commutative structure sheaf on the standard big `τ`-site of
`S`. -/
noncomputable def bigCommStructureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Sheaf (τ.overTopology S) CommRingCat.{u + 1} :=
  ⟨Scheme.Over.commStructurePresheaf (Functor.id (Over S)),
    bigCommStructurePresheaf_isSheaf τ S⟩

/-- The underlying presheaf of `bigCommStructureSheaf τ S` is the lifted
commutative global-functions presheaf. -/
theorem bigCommStructureSheaf_obj (τ : StandardTopology) (S : Scheme.{u}) :
    (bigCommStructureSheaf τ S).obj =
      Scheme.Over.commStructurePresheaf (Functor.id (Over S)) := sorry

/-- The lifted pullback-sections presheaf is a sheaf on a standard big site. -/
theorem bigCommPresheaf_isSheaf (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (τ.overTopology S)
      (Scheme.Modules.commPullbackSectionsPresheaf
        (Functor.id (Over S)) F).presheaf := sorry

/-- The associated module on a standard big site, over its lifted commutative
structure sheaf. -/
noncomputable def bigComm (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (τ.overTopology S) (bigCommStructureSheaf τ S) :=
  ⟨Scheme.Modules.commPullbackSectionsPresheaf (Functor.id (Over S)) F,
    bigCommPresheaf_isSheaf τ S F⟩

/-- The underlying module presheaf of `bigComm τ S F` is the lifted
pullback-sections presheaf. -/
theorem bigComm_val (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (bigComm τ S F).val =
      Scheme.Modules.commPullbackSectionsPresheaf (Functor.id (Over S)) F := sorry

/-- The lifted commutative global-functions presheaf is a sheaf on a selected
small Zariski or étale site. -/
theorem smallCommStructurePresheaf_isSheaf
    (σ : SmallStandardTopology) (S : Scheme.{u}) :
    Presheaf.IsSheaf (σ.topology S)
      (Scheme.Over.commStructurePresheaf (σ.toOver S)) := sorry

/-- The lifted commutative structure sheaf on the selected small standard site
of `S`. -/
noncomputable def smallCommStructureSheaf
    (σ : SmallStandardTopology) (S : Scheme.{u}) :
    Sheaf (σ.topology S) CommRingCat.{u + 1} :=
  ⟨Scheme.Over.commStructurePresheaf (σ.toOver S),
    smallCommStructurePresheaf_isSheaf σ S⟩

/-- The underlying presheaf of `smallCommStructureSheaf σ S` is the lifted
commutative global-functions presheaf. -/
theorem smallCommStructureSheaf_obj
    (σ : SmallStandardTopology) (S : Scheme.{u}) :
    (smallCommStructureSheaf σ S).obj =
      Scheme.Over.commStructurePresheaf (σ.toOver S) := sorry

/-- The lifted pullback-sections presheaf is a sheaf on a selected small
standard site. -/
theorem smallCommPresheaf_isSheaf
    (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (σ.topology S)
      (Scheme.Modules.commPullbackSectionsPresheaf (σ.toOver S) F).presheaf := sorry

/-- The associated module on a selected small standard site, over its lifted
commutative structure sheaf. -/
noncomputable def smallComm (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (σ.topology S) (smallCommStructureSheaf σ S) :=
  ⟨Scheme.Modules.commPullbackSectionsPresheaf (σ.toOver S) F,
    smallCommPresheaf_isSheaf σ S F⟩

/-- The underlying module presheaf of `smallComm σ S F` is the lifted
pullback-sections presheaf. -/
theorem smallComm_val (σ : SmallStandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (smallComm σ S F).val =
      Scheme.Modules.commPullbackSectionsPresheaf (σ.toOver S) F := sorry

namespace StandardSmall

/-- The lifted commutative global-functions presheaf is a sheaf on every
small standard site. -/
theorem commStructurePresheafIsSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Presheaf.IsSheaf (StandardTopology.Small.topology τ S)
      (Scheme.Over.commStructurePresheaf
        (StandardTopology.Small.toOver τ S)) := sorry

/-- The lifted commutative structure sheaf on the small `τ`-site of `S`. -/
noncomputable def commStructureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Sheaf (StandardTopology.Small.topology τ S) CommRingCat.{u + 1} :=
  ⟨Scheme.Over.commStructurePresheaf (StandardTopology.Small.toOver τ S),
    commStructurePresheafIsSheaf τ S⟩

/-- The underlying presheaf of the lifted commutative structure sheaf is the
lifted global-functions presheaf. -/
theorem commStructureSheaf_obj (τ : StandardTopology) (S : Scheme.{u}) :
    (commStructureSheaf τ S).obj =
      Scheme.Over.commStructurePresheaf
        (StandardTopology.Small.toOver τ S) := sorry

/-- The lifted pullback-sections presheaf is a sheaf on every small standard
site. -/
theorem commPresheafIsSheaf (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (StandardTopology.Small.topology τ S)
      (Scheme.Modules.commPullbackSectionsPresheaf
        (StandardTopology.Small.toOver τ S) F).presheaf := sorry

/-- The associated module on the small `τ`-site over its lifted commutative
structure sheaf. -/
noncomputable def comm (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules.RingedSite.ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (StandardTopology.Small.topology τ S) (commStructureSheaf τ S) :=
  ⟨Scheme.Modules.commPullbackSectionsPresheaf
      (StandardTopology.Small.toOver τ S) F,
    commPresheafIsSheaf τ S F⟩

/-- The underlying module presheaf is the lifted pullback-sections
presheaf. -/
theorem comm_val (τ : StandardTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    (comm τ S F).val = Scheme.Modules.commPullbackSectionsPresheaf
      (StandardTopology.Small.toOver τ S) F := sorry

end StandardSmall

end AlgebraicGeometry.Scheme.AssociatedModule
