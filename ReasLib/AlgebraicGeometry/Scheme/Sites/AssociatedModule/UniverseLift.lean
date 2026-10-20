/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Sheafification.Lifted
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Ambient
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing

/-!
# Universe lifts of associated modules

This module packages the commutative-ring presentations of standard scheme
sites and the conservative universe-lift functors from ordinary module sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The lifted commutative-ring presentation of a standard big ringed site. -/
noncomputable abbrev bigCommRingedSite (τ : StandardTopology) (S : Scheme.{u}) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommRingSheaf (τ.overTopology S) (bigCommStructureSheaf τ S)

/-- The lifted big ringed site unfolds to its commutative structure-sheaf
presentation. -/
theorem bigCommRingedSite_def (τ : StandardTopology) (S : Scheme.{u}) :
    bigCommRingedSite τ S =
      RingedSite.ofCommRingSheaf (τ.overTopology S)
        (bigCommStructureSheaf τ S) := sorry

/-- The lifted commutative-ring presentation of a small standard ringed site. -/
noncomputable abbrev smallCommRingedSite
    (τ : StandardTopology) (S : Scheme.{u}) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommRingSheaf (StandardTopology.Small.topology τ S)
    (StandardSmall.commStructureSheaf τ S)

/-- The lifted small ringed site unfolds to its commutative structure-sheaf
presentation. -/
theorem smallCommRingedSite_def (τ : StandardTopology) (S : Scheme.{u}) :
    smallCommRingedSite τ S =
      RingedSite.ofCommRingSheaf (StandardTopology.Small.topology τ S)
        (StandardSmall.commStructureSheaf τ S) := sorry

/-- The universe lift of one value of a module presheaf over a scheme site. -/
noncomputable abbrev liftedModuleObj {C : Type (u + 1)} [Category.{u} C]
    {S : Scheme.{u}} (p : C ⥤ Over S)
    (M : _root_.PresheafOfModules (Scheme.Over.structurePresheaf p))
    (U : Cᵒᵖ) : ModuleCat.{u + 1} ((Scheme.Over.commStructurePresheaf p).obj U) :=
  (ModuleCat.restrictScalars (ULift.ringEquiv.{u, u + 1}).toRingHom).obj
    ((ModuleCat.uliftFunctor.{u + 1, u}
      ((Scheme.Over.structurePresheaf p).obj U)).obj (M.obj U))

/-- The universe-lifted action of a module-presheaf morphism preserves addition. -/
theorem liftedModuleMap_add {C : Type (u + 1)} [Category.{u} C]
    {S : Scheme.{u}} (p : C ⥤ Over S)
    {M N : _root_.PresheafOfModules (Scheme.Over.structurePresheaf p)}
    (f : M ⟶ N) (U : Cᵒᵖ) (x y : liftedModuleObj p M U) :
    ULift.up (f.app U (x + y).down) =
      ULift.up (f.app U x.down) + ULift.up (f.app U y.down) := sorry

/-- The universe-lifted action of a module-presheaf morphism preserves scalar
multiplication. -/
theorem liftedModuleMap_smul {C : Type (u + 1)} [Category.{u} C]
    {S : Scheme.{u}} (p : C ⥤ Over S)
    {M N : _root_.PresheafOfModules (Scheme.Over.structurePresheaf p)}
    (f : M ⟶ N) (U : Cᵒᵖ)
    (r : (Scheme.Over.commStructurePresheaf p).obj U)
    (x : liftedModuleObj p M U) :
    (ULift.up (f.app U (r • x).down) : liftedModuleObj p N U) =
      @SMul.smul ((Scheme.Over.commStructurePresheaf p).obj U)
        (liftedModuleObj p N U) (ModuleCat.isModule (liftedModuleObj p N U)).toSMul r
        (ULift.up (f.app U x.down)) := sorry

/-- The universe lift of a component of a module-presheaf morphism. -/
noncomputable def liftedModuleMap {C : Type (u + 1)} [Category.{u} C]
    {S : Scheme.{u}} (p : C ⥤ Over S)
    {M N : _root_.PresheafOfModules (Scheme.Over.structurePresheaf p)}
    (f : M ⟶ N) (U : Cᵒᵖ) : liftedModuleObj p M U ⟶ liftedModuleObj p N U :=
  let source : ModuleCat.{u + 1} ((Scheme.Over.commStructurePresheaf p).obj U) :=
    liftedModuleObj p M U
  let target : ModuleCat.{u + 1} ((Scheme.Over.commStructurePresheaf p).obj U) :=
    liftedModuleObj p N U
  @ModuleCat.ofHom ((Scheme.Over.commStructurePresheaf p).obj U) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ ULift.up (f.app U x.down)
      map_add' := liftedModuleMap_add p f U
      map_smul' := liftedModuleMap_smul p f U }

/-- The scalar-restricted target of a lifted module-presheaf restriction map. -/
noncomputable abbrev liftedModuleRestrictionTarget
    {C : Type (u + 1)} [Category.{u} C] {S : Scheme.{u}} (p : C ⥤ Over S)
    (M : _root_.PresheafOfModules (Scheme.Over.structurePresheaf p))
    {U V : Cᵒᵖ} (f : U ⟶ V) :=
  (ModuleCat.restrictScalars
    ((Scheme.Over.commStructurePresheaf p).map f).hom).obj (liftedModuleObj p M V)

/-- A lifted module-presheaf restriction map preserves addition. -/
theorem liftedModuleRestrictionMap_add
    {C : Type (u + 1)} [Category.{u} C] {S : Scheme.{u}} (p : C ⥤ Over S)
    (M : _root_.PresheafOfModules (Scheme.Over.structurePresheaf p))
    {U V : Cᵒᵖ} (f : U ⟶ V) (x y : liftedModuleObj p M U) :
    (ULift.up (M.map f (x + y).down) : liftedModuleRestrictionTarget p M f) =
      ULift.up (M.map f x.down) + ULift.up (M.map f y.down) := sorry

/-- A lifted module-presheaf restriction map preserves scalar multiplication. -/
theorem liftedModuleRestrictionMap_smul
    {C : Type (u + 1)} [Category.{u} C] {S : Scheme.{u}} (p : C ⥤ Over S)
    (M : _root_.PresheafOfModules (Scheme.Over.structurePresheaf p))
    {U V : Cᵒᵖ} (f : U ⟶ V)
    (r : (Scheme.Over.commStructurePresheaf p).obj U)
    (x : liftedModuleObj p M U) :
    (ULift.up (M.map f (r • x).down) : liftedModuleRestrictionTarget p M f) =
      @SMul.smul ((Scheme.Over.commStructurePresheaf p).obj U)
        (liftedModuleRestrictionTarget p M f)
        (ModuleCat.isModule (liftedModuleRestrictionTarget p M f)).toSMul r
        (ULift.up (M.map f x.down)) := sorry

/-- The universe lift of a module-presheaf restriction map. -/
noncomputable def liftedModuleRestrictionMap
    {C : Type (u + 1)} [Category.{u} C] {S : Scheme.{u}} (p : C ⥤ Over S)
    (M : _root_.PresheafOfModules (Scheme.Over.structurePresheaf p))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    liftedModuleObj p M U ⟶ liftedModuleRestrictionTarget p M f :=
  let source : ModuleCat.{u + 1} ((Scheme.Over.commStructurePresheaf p).obj U) :=
    liftedModuleObj p M U
  let target : ModuleCat.{u + 1} ((Scheme.Over.commStructurePresheaf p).obj U) :=
    liftedModuleRestrictionTarget p M f
  @ModuleCat.ofHom ((Scheme.Over.commStructurePresheaf p).obj U) _
    (source : Type _) (target : Type _)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (ModuleCat.isAddCommGroup target) (ModuleCat.isModule target)
    { toFun := fun x ↦ ULift.up (M.map f x.down)
      map_add' := liftedModuleRestrictionMap_add p M f
      map_smul' := liftedModuleRestrictionMap_smul p M f }

/-- The universe lift of a module presheaf over a scheme site. -/
noncomputable def liftedModulePresheaf
    {C : Type (u + 1)} [Category.{u} C] {S : Scheme.{u}} (p : C ⥤ Over S)
    (M : _root_.PresheafOfModules (Scheme.Over.structurePresheaf p)) :
    _root_.PresheafOfModules.{u + 1}
      (CategoryTheory.Presheaf.ringPresheafOfComm
        (Scheme.Over.commStructurePresheaf p)) where
  obj U := liftedModuleObj p M U
  map f := liftedModuleRestrictionMap p M f
  map_id := sorry
  map_comp := sorry

/-- The universe lift of a morphism of module presheaves. -/
noncomputable def liftedModuleNatTrans
    {C : Type (u + 1)} [Category.{u} C] {S : Scheme.{u}} (p : C ⥤ Over S)
    {M N : _root_.PresheafOfModules (Scheme.Over.structurePresheaf p)}
    (f : M ⟶ N) : liftedModulePresheaf p M ⟶ liftedModulePresheaf p N where
  app U := liftedModuleMap p f U
  naturality := sorry

/-- Universe lifting preserves the sheaf condition on a big associated-module
site. -/
theorem bigModuleLiftIsSheaf (S : Scheme.{u}) (τ : StandardTopology)
    (M : SheafOfModules (bigStructureSheaf τ S)) :
    Presheaf.IsSheaf (τ.overTopology S)
      (liftedModulePresheaf (𝟭 (Over S)) M.val).presheaf := sorry

/-- The universe lift of an object of a big associated-module category. -/
noncomputable def bigModuleLiftObj (S : Scheme.{u}) (τ : StandardTopology)
    (M : SheafOfModules (bigStructureSheaf τ S)) :
    RingedSite.ModuleCat.{u + 1} (bigCommRingedSite τ S) :=
  ⟨liftedModulePresheaf (𝟭 (Over S)) M.val, bigModuleLiftIsSheaf S τ M⟩

/-- The universe lift of a morphism in a big associated-module category. -/
noncomputable def bigModuleLiftMap (S : Scheme.{u}) (τ : StandardTopology)
    {M N : SheafOfModules (bigStructureSheaf τ S)} (f : M ⟶ N) :
    bigModuleLiftObj S τ M ⟶ bigModuleLiftObj S τ N :=
  ⟨liftedModuleNatTrans (𝟭 (Over S)) f.val⟩

/-- The functorial universe lift of big-site module sheaves to their
commutative presentation. -/
noncomputable def bigModuleLift (S : Scheme.{u}) (τ : StandardTopology) :
    SheafOfModules (bigStructureSheaf τ S) ⥤
      RingedSite.ModuleCat.{u + 1} (bigCommRingedSite τ S) where
  obj := bigModuleLiftObj S τ
  map := bigModuleLiftMap S τ
  map_id := sorry
  map_comp := sorry

/-- Universe lifting preserves the sheaf condition on every small standard
associated-module site. -/
theorem smallModuleLiftIsSheaf (S : Scheme.{u}) (τ : StandardTopology)
    (M : SheafOfModules (StandardSmall.structureSheaf τ S)) :
    Presheaf.IsSheaf (StandardTopology.Small.topology τ S)
      (liftedModulePresheaf (StandardTopology.Small.toOver τ S) M.val).presheaf := sorry

/-- The universe lift of an object of a small standard associated-module category. -/
noncomputable def smallModuleLiftObj (S : Scheme.{u}) (τ : StandardTopology)
    (M : SheafOfModules (StandardSmall.structureSheaf τ S)) :
    RingedSite.ModuleCat.{u + 1} (smallCommRingedSite τ S) :=
  ⟨liftedModulePresheaf (StandardTopology.Small.toOver τ S) M.val,
    smallModuleLiftIsSheaf S τ M⟩

/-- The universe lift of a morphism in a small standard associated-module category. -/
noncomputable def smallModuleLiftMap (S : Scheme.{u}) (τ : StandardTopology)
    {M N : SheafOfModules (StandardSmall.structureSheaf τ S)} (f : M ⟶ N) :
    smallModuleLiftObj S τ M ⟶ smallModuleLiftObj S τ N :=
  ⟨liftedModuleNatTrans (StandardTopology.Small.toOver τ S) f.val⟩

/-- The functorial universe lift of small-standard-site module sheaves to their
commutative presentation. -/
noncomputable def smallModuleLift (S : Scheme.{u}) (τ : StandardTopology) :
    SheafOfModules (StandardSmall.structureSheaf τ S) ⥤
      RingedSite.ModuleCat.{u + 1} (smallCommRingedSite τ S) where
  obj := smallModuleLiftObj S τ
  map := smallModuleLiftMap S τ
  map_id := sorry
  map_comp := sorry

/-- The universe lift of an ordinary big associated module is canonically
isomorphic to its commutative presentation. -/
noncomputable def bigModuleLiftIso (S : Scheme.{u}) (τ : StandardTopology)
    (F : Scheme.QCoh S) :
    (bigModuleLift S τ).obj ((bigModuleFunctor S τ).obj F) ≅ bigComm τ S F.obj :=
  Iso.refl _

/-- The forward map of the big associated-module lift isomorphism is the
identity under the canonical presentation. -/
theorem bigModuleLiftIso_hom (S : Scheme.{u}) (τ : StandardTopology)
    (F : Scheme.QCoh S) : (bigModuleLiftIso S τ F).hom = 𝟙 _ := sorry

/-- Universe lifting of big-site module sheaves reflects isomorphisms. -/
instance bigModuleLiftReflectsIsomorphisms
    (S : Scheme.{u}) (τ : StandardTopology) :
    (bigModuleLift S τ).ReflectsIsomorphisms := sorry

/-- A morphism of ordinary big-site module sheaves is invertible exactly when
its universe lift is invertible. -/
theorem bigModuleLift_isIso_iff (S : Scheme.{u}) (τ : StandardTopology)
    {M N : SheafOfModules (bigStructureSheaf τ S)} (f : M ⟶ N) :
    IsIso ((bigModuleLift S τ).map f) ↔ IsIso f := sorry

/-- The universe lift of an ordinary small associated module is canonically
isomorphic to its commutative presentation. -/
noncomputable def smallModuleLiftIso (S : Scheme.{u}) (τ : StandardTopology)
    (F : Scheme.QCoh S) :
    (smallModuleLift S τ).obj ((smallModuleFunctor S τ).obj F) ≅
      StandardSmall.comm τ S F.obj :=
  Iso.refl _

/-- The forward map of the small associated-module lift isomorphism is the
identity under the canonical presentation. -/
theorem smallModuleLiftIso_hom (S : Scheme.{u}) (τ : StandardTopology)
    (F : Scheme.QCoh S) : (smallModuleLiftIso S τ F).hom = 𝟙 _ := sorry

/-- Universe lifting of small-standard-site module sheaves reflects
isomorphisms. -/
instance smallModuleLiftReflectsIsomorphisms
    (S : Scheme.{u}) (τ : StandardTopology) :
    (smallModuleLift S τ).ReflectsIsomorphisms := sorry

/-- A morphism of ordinary small-standard-site module sheaves is invertible
exactly when its universe lift is invertible. -/
theorem smallModuleLift_isIso_iff (S : Scheme.{u}) (τ : StandardTopology)
    {M N : SheafOfModules (StandardSmall.structureSheaf τ S)} (f : M ⟶ N) :
    IsIso ((smallModuleLift S τ).map f) ↔ IsIso f := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
