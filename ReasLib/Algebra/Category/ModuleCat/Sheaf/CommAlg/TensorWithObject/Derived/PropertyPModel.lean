/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.StandardDerived
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Triangulated
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Enriched

/-!
# Actual property-P model for derived tensor

The specified all-pairs replacement is first descended to homotopy classes. Tensoring its
weak equivalences gives actual underlying cochain quasi-isomorphisms. Their literal reverse
localization edges supply every inverse below; no total-derived existence or IsIso certificate
supplies data. This leaf does not claim the downstream tensor-Hom adjunction or shift data.
-/

@[expose] public section
noncomputable section
universe r u v w z
open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject.Derived.PropertyPModel
attribute [local instance] RingedSite.Hom.RingPresentation.moduleHasDerivedCategory
variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

abbrev sourceFunctor (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.sourceFunctor (TensorWithObject.homotopyFunctor K)

abbrev computed (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.computed (TensorWithObject.homotopyFunctor K)

abbrev denominatorMap (K : Complex.{r, u, v, w, max u z} O)
    {X Y : DifferentialGradedCategory.K R (TensorWithObject.Modules K)} (f : X ⟶ Y) :=
  DifferentialGradedModule.PropertyP.StandardDerived.denominatorMap (TensorWithObject.homotopyFunctor K) f

abbrev denominatorMap_mem_quasiIso (K : Complex.{r, u, v, w, max u z} O)
    {X Y : DifferentialGradedCategory.K R (TensorWithObject.Modules K)} (f : X ⟶ Y)
    (hf : (DifferentialGradedModule.Homotopy.acyclic (endDGA K)).trW f) :=
  DifferentialGradedModule.PropertyP.StandardDerived.denominatorMap_mem_quasiIso (TensorWithObject.homotopyFunctor K) f hf

abbrev onPaths (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.onPaths (TensorWithObject.homotopyFunctor K)

abbrev tensorFunctor (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.functor (TensorWithObject.homotopyFunctor K)

abbrev computationIso (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.computationIso (TensorWithObject.homotopyFunctor K)

abbrev tensorCounit (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.counit (TensorWithObject.homotopyFunctor K)

abbrev tensorCounit_app (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.counit_app (TensorWithObject.homotopyFunctor K)

abbrev augmentationMap (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.augmentationMap (TensorWithObject.homotopyFunctor K)

abbrev augmentationMap_mem_quasiIso (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.augmentationMap_mem_quasiIso (TensorWithObject.homotopyFunctor K)

abbrev tensorCounitAppIso (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.counitAppIso (TensorWithObject.homotopyFunctor K)

abbrev tensorCounitAppIso_hom (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.counitAppIso_hom (TensorWithObject.homotopyFunctor K)

/-- Computation in the strict tensor complex, including both actual comparison arrows. -/
def tensorModelIso (K : Complex.{r, u, v, w, max u z} O)
    (M : TensorWithObject.Modules K) (hM : DifferentialGradedModule.HasPropertyP (endDGA K) M) :
    (tensorFunctor K).obj ((DifferentialGradedModule.Derived.fromModules (endDGA K)).obj M) ≅
      DerivedCategory.Q.obj ((TensorWithObject.tensorFunctor K).obj M) :=
  tensorCounitAppIso K M hM ≪≫
    (DerivedCategory.quotientCompQhIso
      (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)).app
        ((TensorWithObject.tensorFunctor K).obj M)

/-- Certify the actual model without selecting its data. -/
abbrev tensorFunctor_isLeftDerived (K : Complex.{r, u, v, w, max u z} O) :=
  DifferentialGradedModule.PropertyP.StandardDerived.isLeftDerived (TensorWithObject.homotopyFunctor K)
end SheafOfModules.CommAlg.TensorWithObject.Derived.PropertyPModel
