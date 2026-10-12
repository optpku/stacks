/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift

/-!
# Tensor products of associated modules

This module constructs the canonical comparison morphisms between associated
modules of tensor products and tensor products of associated modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite.SectionBilinearMap
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The tensor product of two quasi-coherent scheme modules, bundled as a
quasi-coherent module. -/
noncomputable def quasicoherentTensor (S : Scheme.{u}) (F G : Scheme.QCoh S) :
    Scheme.QCoh S :=
  ⟨F.obj ⊗ G.obj,
    @SheafOfModules.IsQuasicoherent.tensor _ _ _ _ _ _ _ _ _
      F.obj G.obj F.property G.property⟩

/-- The underlying module of the bundled quasi-coherent tensor product is the
ordinary tensor product. -/
theorem quasicoherentTensor_obj (S : Scheme.{u}) (F G : Scheme.QCoh S) :
    (quasicoherentTensor S F G).obj = F.obj ⊗ G.obj := sorry

/-- The tensor unit of scheme modules is quasi-coherent. -/
theorem tensorUnitIsQuasicoherent (S : Scheme.{u}) :
    SheafOfModules.IsQuasicoherent (𝟙_ S.Modules) := sorry

/-- The structure module of a scheme as an object of its quasi-coherent
category. -/
noncomputable def structureModule (S : Scheme.{u}) : Scheme.QCoh S :=
  ⟨𝟙_ S.Modules, tensorUnitIsQuasicoherent S⟩

/-- The underlying module of the bundled structure module is the tensor unit. -/
theorem structureModule_obj (S : Scheme.{u}) :
    (structureModule S).obj = 𝟙_ S.Modules := sorry

/-- Tensor two pullback sections and transport along the canonical scheme
pullback tensor isomorphism. -/
noncomputable def pullbackTensorSection
    {C : Type (u + 1)} [Category.{u} C] {S : Scheme.{u}} (p : C ⥤ Over S)
    (F G : S.Modules) (U : Cᵒᵖ) (x : Scheme.Modules.pullbackSectionsObj p F U)
    (y : Scheme.Modules.pullbackSectionsObj p G U) :
    Scheme.Modules.pullbackSectionsObj p (F ⊗ G) U :=
  (SheafOfModules.sectionsMap
    (Scheme.Modules.pullbackTensorIso (p.obj U.unop).hom F G).inv
    (AlgebraicGeometry.RingedSpace.tensorSection
      (RingedSpace.sectionFromTop
        ((Scheme.Modules.pullback (p.obj U.unop).hom).obj F) x)
      (RingedSpace.sectionFromTop
        ((Scheme.Modules.pullback (p.obj U.unop).hom).obj G) y))).1 (Opposite.op ⊤)

/-- The lifted sectionwise tensor pairing for associated modules. -/
noncomputable def commTensorBilinear
    {C : Type (u + 1)} [Category.{u} C] {S : Scheme.{u}} (p : C ⥤ Over S)
    (F G : S.Modules) :
    PresheafOfModules.BilinearMap (Scheme.Over.commStructurePresheaf p)
      (Scheme.Modules.commPullbackSectionsPresheaf p F)
      (Scheme.Modules.commPullbackSectionsPresheaf p G)
      (Scheme.Modules.commPullbackSectionsPresheaf p (F ⊗ G)) where
  app U :=
    { toFun := fun x ↦
        { toFun := fun y ↦ ULift.up (pullbackTensorSection p F G U x.down y.down)
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- The canonical tensor comparison on the commutative presentation of big
associated modules. -/
noncomputable def bigTensorComparison (S : Scheme.{u}) (τ : StandardTopology)
    (F G : Scheme.QCoh S) :
    bigComm τ S F.obj ⊗ bigComm τ S G.obj ⟶
      bigComm τ S (quasicoherentTensor S F G).obj :=
  hom.{u + 1, u} (commTensorBilinear (𝟭 (Over S)) F.obj G.obj)

/-- The canonical tensor comparison on the commutative presentation of small
standard-site associated modules. -/
noncomputable def smallTensorComparison
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S) :
    StandardSmall.comm τ S F.obj ⊗ StandardSmall.comm τ S G.obj ⟶
      StandardSmall.comm τ S (quasicoherentTensor S F G).obj :=
  hom.{u + 1, u}
    (commTensorBilinear (StandardTopology.Small.toOver τ S) F.obj G.obj)

/-- The tensor comparison for ordinary big associated modules, displayed
after the conservative universe lift. -/
noncomputable def bigModuleTensorComparison
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S) :
    (bigModuleLift S τ).obj ((bigModuleFunctor S τ).obj F) ⊗
        (bigModuleLift S τ).obj ((bigModuleFunctor S τ).obj G) ⟶
      (bigModuleLift S τ).obj
        ((bigModuleFunctor S τ).obj (quasicoherentTensor S F G)) :=
  (tensorIso (bigModuleLiftIso S τ F) (bigModuleLiftIso S τ G)).hom ≫
    bigTensorComparison S τ F G ≫
      (bigModuleLiftIso S τ (quasicoherentTensor S F G)).inv

/-- Invertibility of the ordinary big tensor comparison after universe lifting
is equivalent to invertibility of its commutative presentation. -/
theorem bigModuleTensorComparison_isIso_iff
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S) :
    IsIso (bigModuleTensorComparison S τ F G) ↔
      IsIso (bigTensorComparison S τ F G) := sorry

/-- The tensor comparison for ordinary small-standard-site associated modules,
displayed after the conservative universe lift. -/
noncomputable def smallModuleTensorComparison
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S) :
    (smallModuleLift S τ).obj ((smallModuleFunctor S τ).obj F) ⊗
        (smallModuleLift S τ).obj ((smallModuleFunctor S τ).obj G) ⟶
      (smallModuleLift S τ).obj
        ((smallModuleFunctor S τ).obj (quasicoherentTensor S F G)) :=
  (tensorIso (smallModuleLiftIso S τ F) (smallModuleLiftIso S τ G)).hom ≫
    smallTensorComparison S τ F G ≫
      (smallModuleLiftIso S τ (quasicoherentTensor S F G)).inv

/-- Invertibility of the ordinary small-site tensor comparison after universe
lifting is equivalent to invertibility of its commutative presentation. -/
theorem smallModuleTensorComparison_isIso_iff
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S) :
    IsIso (smallModuleTensorComparison S τ F G) ↔
      IsIso (smallTensorComparison S τ F G) := sorry

/-- The canonical big-site tensor comparison is invertible. -/
instance bigTensorComparisonIsIso (S : Scheme.{u}) (τ : StandardTopology)
    (F G : Scheme.QCoh S) : IsIso (bigModuleTensorComparison S τ F G) := sorry

/-- The canonical small-standard-site tensor comparison is invertible. -/
instance smallTensorComparisonIsIso
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S) :
    IsIso (smallModuleTensorComparison S τ F G) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
