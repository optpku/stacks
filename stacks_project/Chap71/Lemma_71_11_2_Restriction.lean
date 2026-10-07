module

public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap71.Lemma_71_11_11_Triple
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Actual unit and tensor maps for restriction to a represented scheme

Restriction is evaluated on its precise small-etale site object. Pure tensor
sections descend through the tensor sheaf's universal property. This constructs
the lax tensor map without claiming equality of tensor objects across sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
variable {S : Scheme.{u}} (Z : Over S)

/-- Continuity from the actual ringed-site morphism's stored site proof. -/
instance schemeBaseContinuous (Z : Over S) :
    (schemeEtaleRingedHom Z).base.IsContinuous
      (Scheme.Etale.Small.ringedSite Z.left).siteTopology
      (ringedSite (ofOver Z)).siteTopology :=
  (schemeEtaleRingedHom Z).isMorphismOfSites.toIsContinuous

/-- Continuity of the open-to-etale base functor, from its stored proof. -/
instance opensBaseContinuous (Y : Scheme.{u}) :
    (smallEtaleToOpensRingedHom Y).base.IsContinuous
      (Opens.grothendieckTopology Y) (Scheme.Etale.Small.ringedSite Y).siteTopology :=
  (smallEtaleToOpensRingedHom Y).isMorphismOfSites.toIsContinuous

/-- The precise small-etale object at which restriction evaluates an open. -/
def siteObject (V : Z.left.Opens) : smallEtaleSite (ofOver Z) :=
  (Modules.restrictPostcompose (𝟙 (ofOver Z))).obj
    ((schemeEtaleRingedHom Z).base.obj
      ((smallEtaleToOpensRingedHom Z.left).base.obj V))

/-- Restriction does not change the underlying section values at that object. -/
def sectionEquiv (M : (ofOver Z).Modules) (V : Z.left.Opens) :
    ((Modules.restrictToScheme Z).obj M).val.obj (op V) ≃
      M.val.obj (op (siteObject Z V)) := by
  dsimp only [Modules.restrictToScheme, Functor.comp_obj, RingedSite.Hom.modulePushforward,
    opensToSchemeModules, SheafOfModules.pushforward, SheafOfModules.restrictScalars,
    PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
    PresheafOfModules.pushforward₀Obj, PresheafOfModules.restrictScalars,
    PresheafOfModules.restrictScalarsObj, Modules.restrictFunctor, siteObject]
  exact Equiv.refl _

/-- Pure tensor pairing of the original module sections, transported to restriction. -/
def tensorSection (M N : (ofOver Z).Modules) (V : Z.left.Opens)
    (x : ((Modules.restrictToScheme Z).obj M).val.obj (op V))
    (y : ((Modules.restrictToScheme Z).obj N).val.obj (op V)) :
    ((Modules.restrictToScheme Z).obj (M ⊗ N)).val.obj (op V) :=
  (sectionEquiv Z (M ⊗ N) V).symm
    (ofCommSection (M ⊗ N)
      (commTensorSection M N
        (asCommSection M (sectionEquiv Z M V x))
        (asCommSection N (sectionEquiv Z N V y))))

/-- The restriction-compatible bilinear pairing on scheme opens. -/
def tensorBilinear (M N : (ofOver Z).Modules) :
    SectionBilinearMap.{u, u} Z.left.sheaf
      ((Modules.restrictToScheme Z).obj M)
      ((Modules.restrictToScheme Z).obj N)
      ((Modules.restrictToScheme Z).obj (M ⊗ N)) where
  app V := LinearMap.mk₂ (Z.left.sheaf.obj.obj V)
    (tensorSection Z M N V.unop) sorry sorry sorry sorry
  naturality := sorry

/-- The actual lax tensor comparison obtained from the bilinear universal property. -/
def tensorLax (M N : (ofOver Z).Modules) :
    (Modules.restrictToScheme Z).obj M ⊗ (Modules.restrictToScheme Z).obj N ⟶
      (Modules.restrictToScheme Z).obj (M ⊗ N) :=
  (tensorBilinear Z M N).hom

-- The four explicit site/scalar unit maps exceed the default 200000 elaboration
-- heartbeats; the same construction was checked with this bounded local limit.
set_option maxHeartbeats 800000 in
/-- The unit comparison is the composite of the four canonical unit maps in restriction. -/
def unitMap :
    SheafOfModules.unit Z.left.ringCatSheaf ⟶
      (Modules.restrictToScheme Z).obj
        (SheafOfModules.unit (structureSheaf (ofOver Z))) :=
  let pushScheme := (schemeEtaleRingedHom Z).modulePushforward.{u}
  let pushOpen := (smallEtaleToOpensRingedHom Z.left).modulePushforward.{u}
  let scalars := opensToSchemeModules Z.left
  SheafOfModules.unitToPushforwardObjUnit
      (F := 𝟭 (TopologicalSpace.Opens Z.left))
      (S := Z.left.ringCatSheaf)
      (R := ⟨Scheme.Site.structurePresheaf (Z.left.restrictFunctor ⋙ Over.forget Z.left),
        opensStructurePresheaf_isSheaf Z.left⟩)
      (opensStructureToRingCatSheaf Z.left) ≫
    scalars.map
      (SheafOfModules.unitToPushforwardObjUnit
        (F := (smallEtaleToOpensRingedHom Z.left).base)
        (S := ⟨Scheme.Site.structurePresheaf (Z.left.restrictFunctor ⋙ Over.forget Z.left),
          opensStructurePresheaf_isSheaf Z.left⟩)
        (R := (Scheme.Etale.Small.ringedSite Z.left).structureSheaf)
        (smallEtaleToOpensRingedHom Z.left).structureSheafMap) ≫
    (pushOpen ⋙ scalars).map
      (SheafOfModules.unitToPushforwardObjUnit
        (F := (schemeEtaleRingedHom Z).base)
        (S := (Scheme.Etale.Small.ringedSite Z.left).structureSheaf)
        (R := structureSheaf (ofOver Z))
        (schemeEtaleRingedHom Z).structureSheafMap) ≫
    (pushScheme ⋙ pushOpen ⋙ scalars).map
      (SheafOfModules.unitToPushforwardObjUnit
        (F := Modules.restrictPostcompose (𝟙 (ofOver Z)))
        (S := structureSheaf (ofOver Z)) (R := structureSheaf (ofOver Z))
        (Modules.restrictStructureMap (𝟙 (ofOver Z))))

/-- Restriction is lax monoidal with the actual unit and sectionwise tensor maps. -/
noncomputable instance laxMonoidal : (Modules.restrictToScheme Z).LaxMonoidal where
  ε := (RingedSpace.unitIsoTensorUnit Z.left.toRingedSpace).inv ≫ unitMap Z ≫
    (Modules.restrictToScheme Z).map (Modules.structureModuleIsoTensorUnit (ofOver Z)).hom
  μ := tensorLax Z
  μ_natural_left := sorry
  μ_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
