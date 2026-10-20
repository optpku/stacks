module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Actual kernel sections and their geometric pullback generators -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Sheaf.InternalModule
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Hom.Conormal
variable {S : Scheme.{u}}

/-- Sections of the fixed categorical ideal kernel as the ordinary kernel of its section map. -/
def idealSectionsIso {Z X : AlgebraicSpace S} (i : Z ⟶ X)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (idealSheaf i).val.obj U ≅
      ModuleCat.of ((structureSheaf X).obj.obj U)
        (LinearMap.ker ((SheafOfModules.evaluation (structureSheaf X) U).map
          (idealSheafMap i)).hom) :=
  (SheafOfModules.evaluation (structureSheaf X) U).mapIso (idealSheaf_spec i) ≪≫
    PreservesKernel.iso (SheafOfModules.evaluation (structureSheaf X) U) (idealSheafMap i) ≪≫
    ModuleCat.kernelIsoKer
      ((SheafOfModules.evaluation (structureSheaf X) U).map (idealSheafMap i))

/-- Sections of an arbitrary module subobject as the actual range of its inclusion.
Injectivity is derived from the supplied categorical monomorphism and evaluation. -/
def subobjectSectionsIso {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : (smallEtaleSite X)ᵒᵖ) :
    I.toModule.val.obj U ≅
      ModuleCat.of ((structureSheaf X).obj.obj U)
        (LinearMap.range ((SheafOfModules.evaluation (structureSheaf X) U).map I.arrow).hom) :=
  (LinearEquiv.ofInjective
    ((SheafOfModules.evaluation (structureSheaf X) U).map I.arrow).hom
    ((ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation (structureSheaf X) U).map I.arrow)).mp inferInstance)).toModuleIso

/-- The identity scheme edge from an étale chart to its postcomposition with an étale map. -/
def restrictionGraph {X Y : AlgebraicSpace S} (e : X ⟶ Y) [Etale e]
    (U : smallEtaleSite X) :
    (smallEtaleToSpaces X).obj U ⟶ (etaleBaseChange e).obj ((etaleRestriction e).obj U) :=
  MorphismProperty.Over.homMk
    (pullback.lift (f := homFunctor e)
      (g := homFunctor ((etaleRestriction e).obj U).hom)
      U.hom (𝟙 (ofOver U.left).functorOfPoints) sorry)
    sorry

/-- A module section on a postcomposed chart gives the actual geometric pullback section,
through the module adjunction unit and the chart evaluation map. -/
def pullbackSection {X Y : AlgebraicSpace S} (e : X ⟶ Y) [Etale e]
    (M : Y.Modules) (U : smallEtaleSite X)
    (s : M.val.obj (op ((etaleRestriction e).obj U))) :
    ((Modules.pullback e).obj M).val.obj (op U) :=
  let M' := (Modules.pullback e).obj M
  let Q := (ToInternal.underlying (structureSheaf X)).obj M'
  (ToInternal.sectionEquiv (structureSheaf X) M' (op U)).symm
    (EtaleTopos.extensionEvaluation X Q (restrictionGraph e U)
      ((((ToInternal.underlying (structureSheaf Y)).map
          ((Modules.pullbackPushforwardAdjunction e).unit.app M) ≫
        (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom e)).hom.app M').hom.app
          (op ((etaleRestriction e).obj U)))
        (ToInternal.sectionEquiv (structureSheaf Y) M (op ((etaleRestriction e).obj U)) s)))

end AlgebraicGeometry.AlgebraicSpace.Hom.Conormal
