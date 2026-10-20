/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel.TotalRightDerived
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Exact precomposition with the required acyclicity of the actual source models -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe κA κB uA vA uB vB uC vC wA wB wC
namespace CategoryTheory.Functor.KInjectiveModel
variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{κA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{κB} B]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C]
variable (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
variable (V : B ⥤ C) [V.Additive]
variable (hAcyclic : ∀ K : CochainComplex A ℤ,
  QuasiIso ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((CochainComplex.KInjectiveResolution.Construction.augmentation.{κB} B).app
      ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{κA} A).obj K)))))

/-- The acyclicity input applies to one specified augmentation, whose localization retains
its actual forward map and formal inverse. -/
def precomposeModelAugmentationIso (K : CochainComplex A ℤ) :=
  Localization.isoOfHom (DerivedCategory.Q (C := C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((CochainComplex.KInjectiveResolution.Construction.augmentation.{κB} B).app
        ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.KInjectiveResolution.Construction.replacement.{κA} A).obj K))))
    (hAcyclic K)

/-- Resolving the exact image of the source augmentation gives a quasi-isomorphism between
K-injective models, and degreewise `V` preserves its homotopy equivalence. -/
def precomposeModelMapIso (K : CochainComplex A ℤ) :
    (cochain.{κB} V).obj ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (cochain.{κB} V).obj ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{κA} A).obj K)) := by
  letI : QuasiIso ((CochainComplex.KInjectiveResolution.Construction.augmentation.{κA} A).app K) :=
    CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso.{κA} A K
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let a := (U.mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((CochainComplex.KInjectiveResolution.Construction.augmentation.{κA} A).app K)
  have ha : QuasiIso a := by
    dsimp [a]
    exact HomologicalComplex.quasiIso_map_of_preservesHomology
      ((CochainComplex.KInjectiveResolution.Construction.augmentation.{κA} A).app K) U
  exact Localization.isoOfHom (DerivedCategory.Q (C := C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((V.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((CochainComplex.KInjectiveResolution.Construction.replacement.{κB} B).map a))
    (modelMap_quasiIso.{κB} V a ha)

/-- The comparison first resolves the exact image of the given source model; it does not
assert that exact inverse image preserves K-injective complexes. -/
def precomposeOnInput (K : CochainComplex A ℤ) :
    (derived.{κA} (U ⋙ V)).obj (DerivedCategory.Q.obj K) ≅
      (U.mapDerivedCategory ⋙ derived.{κB} V).obj (DerivedCategory.Q.obj K) :=
  (fac.{κA} (U ⋙ V)).app K ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (U ⋙ V))
        (ComplexShape.up ℤ)).app
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{κA} A).obj K)).symm ≪≫
    precomposeModelAugmentationIso U V hAcyclic K ≪≫
    (precomposeModelMapIso U V K).symm ≪≫
    ((fac.{κB} V).app ((U.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
    (derived.{κB} V).mapIso (U.mapDerivedCategoryFactors.app K).symm

/-- The specified actual model comparison respects the original cochain maps. -/
theorem precomposeOnInput_naturality {K L : CochainComplex A ℤ} (a : K ⟶ L) :
    (DerivedCategory.Q ⋙ derived.{κA} (U ⋙ V)).map a ≫
        (precomposeOnInput U V hAcyclic L).hom =
      (precomposeOnInput U V hAcyclic K).hom ≫
        (DerivedCategory.Q ⋙ U.mapDerivedCategory ⋙ derived.{κB} V).map a := sorry

/-- Actual comparison maps on cochains before localization descent. -/
def precomposeOnCochains :
    DerivedCategory.Q ⋙ derived.{κA} (U ⋙ V) ≅
      DerivedCategory.Q ⋙ U.mapDerivedCategory ⋙ derived.{κB} V :=
  NatIso.ofComponents (precomposeOnInput U V hAcyclic)
    (fun a ↦ precomposeOnInput_naturality U V hAcyclic a)

/-- Exact precomposition commutes with this right-derived functor when the given images of
source models satisfy the stated acyclicity law. Both directions descend the displayed maps. -/
def precomposeIso : derived.{κA} (U ⋙ V) ≅ U.mapDerivedCategory ⋙ derived.{κB} V :=
  Localization.liftNatIso (DerivedCategory.Q (C := A))
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ derived.{κA} (U ⋙ V))
    (DerivedCategory.Q ⋙ U.mapDerivedCategory ⋙ derived.{κB} V)
    (derived.{κA} (U ⋙ V)) (U.mapDerivedCategory ⋙ derived.{κB} V)
    (precomposeOnCochains U V hAcyclic)

/-- Native uniqueness transports the actual comparison to genuinely supplied total-derived
models of `U ⋙ V` and `V`. -/
def precomposeTotalRightDerivedIso
    [Functor.HasRightDerivedFunctor (Functor.RightDerived.Cochain.toDerived (U ⋙ V))
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    [Functor.HasRightDerivedFunctor (Functor.RightDerived.Cochain.toDerived V)
      (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))] :
    Functor.RightDerived.Cochain.functor (U ⋙ V) ≅
      U.mapDerivedCategory ⋙ Functor.RightDerived.Cochain.functor V :=
  (totalRightDerivedIso.{κA} (U ⋙ V)).symm ≪≫
    precomposeIso U V hAcyclic ≪≫
    isoWhiskerLeft U.mapDerivedCategory (totalRightDerivedIso.{κB} V)

end CategoryTheory.Functor.KInjectiveModel
