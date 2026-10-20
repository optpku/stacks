/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.PresentationComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.LocalComparison
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
