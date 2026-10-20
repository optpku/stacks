/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.RootsModuleSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AcyclicAugmentedComparison
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace ActualRootsHomCohomology
variable {k : Type u} [Field k] (X : SchemeOverField k)
variable (n : ℕ) (hpos : 0 < n) (hn : IsUnit (n : k))
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [X.left.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)) AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)))]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)))]
variable [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)))
variable [hF : Sheaf.IsFiniteTypeLocallyConstantModule F]

/-- The dual coefficient is the actual linear Hom into roots of unity. -/
def dualSheaf := ActualLinearSheafHom.obj X.left (ActualRootsModule.Coeff.{u} n) F (ActualRootsModule.liftedSheaf X.left n)

/-- Resolve the roots coefficient in all module sheaves, then apply local linear Hom. -/
abbrev rootsResolution := injectiveResolution (ActualRootsModule.liftedSheaf X.left n)

abbrev homForget := ActualLinearSheafHom.functor X.left (ActualRootsModule.Coeff.{u} n) F ⋙ ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)

instance homForget_additive : (homForget X n F).Additive := sorry

abbrev complex : CochainComplex (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ :=
  ((homForget X n F).mapHomologicalComplex (ComplexShape.up ℕ)).obj (rootsResolution X n).cocomplex

def augmentation : (ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj (dualSheaf X n F) ⟶
    (complex X n F).X 0 := (homForget X n F).map ((rootsResolution X n).ι.f 0)

theorem augmentation_zero : augmentation X n F ≫ (complex X n F).d 0 1 = 0 := sorry

instance augmentation_mono : Mono (augmentation X n F) := sorry

include hpos hn hF

/-- Locally F is finite over Z/n and μ_n is a rank-one self-injective Z/n
module. Hence the displayed Hom complex resolves the dual sheaf. -/
theorem exactZero :
    (ShortComplex.mk (augmentation X n F) ((complex X n F).d 0 1)
      (augmentation_zero X n F)).Exact := sorry

theorem exactSucc (q : ℕ) :
    (ShortComplex.mk ((complex X n F).d q (q + 1))
      ((complex X n F).d (q + 1) (q + 2))
      ((complex X n F).d_comp_d q (q + 1) (q + 2))).Exact := sorry

omit hpos hn hF

/-- Local Hom into an injective module sheaf is sections-acyclic. No claim
that it is an injective abelian sheaf is used. -/
theorem terms_acyclic (q i : ℕ) :
    IsZero (((ActualSiteExt.abSections X.left).rightDerived (i + 1)).obj ((complex X n F).X q)) := sorry

instance abSections_preservesFiniteLimits : PreservesFiniteLimits (ActualSiteExt.abSections X.left) := sorry

/-- The acyclic resolution comparison uses recursive injective extensions,
with exactness justified for these finite locally constant coefficients. -/
def acyclicIso (i : ℕ) :=
  ActualAcyclicAugmented.homologyIso (complex X n F) (augmentation X n F)
    (augmentation_zero X n F) (exactZero X n hpos hn F) (exactSucc X n hpos hn F)
    (injectiveResolution ((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj (dualSheaf X n F)))
    (ActualSiteExt.abSections X.left) (terms_acyclic X n F) i

/-- At each degree, sections of local linear Hom evaluate to actual module-sheaf morphisms. -/
def sectionsComplexIso :
    ((ActualSiteExt.abSections X.left).mapHomologicalComplex (ComplexShape.up ℕ)).obj (complex X n F) ≅
    ((ActualHomDerivedExt.homFunctor F).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (rootsResolution X n).cocomplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (ActualLinearSheafHom.sectionsHomIso X.left (ActualRootsModule.Coeff.{u} n) F).app ((rootsResolution X n).cocomplex.X q))
    (fun _ _ _ ↦ sorry)

/-- The actual dual-sheaf cohomology to module-Ext comparison. Its map is
acyclic-resolution inversion followed by evaluation of Hom-complex cocycles. -/
def cohomologyExtIso (i : ℕ) :
    AddCommGrpCat.of (((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj (dualSheaf X n F)).H i) ≅
    AddCommGrpCat.of (Ext F (ActualRootsModule.liftedSheaf X.left n) i) :=
  (ActualSiteExt.abDerivedSectionsExtIso X.left
      ((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj (dualSheaf X n F)) i).symm ≪≫
    (acyclicIso X n hpos hn F i).symm ≪≫
    HomologicalComplex.homologyMapIso (sectionsComplexIso X n F) i ≪≫
    ((rootsResolution X n).isoRightDerivedObj (ActualHomDerivedExt.homFunctor F) i).symm ≪≫
    ActualHomDerivedExt.rightDerivedIso F (rootsResolution X n) i

end ActualRootsHomCohomology
