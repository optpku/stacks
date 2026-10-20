/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.InverseSystem
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor.Instances
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison
public import ReasLib.CategoryTheory.Pro.Presentation
public import ReasLib.CategoryTheory.Pro.ModuleLimit

/-!
# The actual tensor-to-ideal-product comparison

The source comparison of duality.tex is the derived tensor counit followed
by multiplication into I^nF. Multiplication is constructed by factoring the
unit action through the image defining the ideal-power product subobject.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.DerivedCategory ComplexShape
open Scheme.Modules Scheme.Modules.IdealPowerComplex
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.TensorComparison

variable {X : Scheme.{u}}

/-- Multiplication of I^nO with F is the ideal inclusion tensored with F,
followed by the tensor-unit action. -/
def action (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) :
    (idealPowerProductSubobject I (𝟙_ X.Modules) n : X.Modules) ⊗ F ⟶ F :=
  ((idealPowerProductSubobject I (𝟙_ X.Modules) n).arrow ⊗ₘ 𝟙 F) ≫ (λ_ F).hom

/-- The actual multiplication factors through the image defining I^nF. -/
theorem action_factors (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) :
    (idealPowerProductSubobject I F n).Factors (action I F n) := sorry

/-- Multiplication into the actual ideal-power product subobject. -/
def termMap (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) :
    (idealPowerProductSubobject I (𝟙_ X.Modules) n : X.Modules) ⊗ F ⟶
      (idealPowerProductSubobject I F n : X.Modules) :=
  (idealPowerProductSubobject I F n).factorThru (action I F n) (action_factors I F n)

/-- The degree-zero cochain ideal stage. -/
def singleStage (I : X.IdealSheafData) (n : ℕ) : CochainComplex X.Modules ℤ :=
  (CochainComplex.singleFunctor X.Modules 0).obj
    (idealPowerProductSubobject I (𝟙_ X.Modules) n : X.Modules)

/-- The termwise ideal-product complex, using the existing filtration owner. -/
def productComplex (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (n : ℕ) :
    CochainComplex X.Modules ℤ :=
  HomologicalComplex.Filtered.Stage.complex (filtered I F) (n : ℤ)

/-- Multiplication on the surviving zero-degree tensor summand. -/
def zeroTermMap (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (n : ℕ) (i : ℤ) :
    (singleStage I n).X 0 ⊗ F.X i ⟶ (productComplex I F n).X i :=
  ((HomologicalComplex.singleObjXSelf (up ℤ) (0 : ℤ)
      (idealPowerProductSubobject I (𝟙_ X.Modules) n : X.Modules)).hom ⊗ₘ 𝟙 (F.X i)) ≫
    termMap I (F.X i) n

/-- The tensor summand map is multiplication when the single-complex index
is zero and the zero map otherwise. -/
def summandMap (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (n : ℕ)
    (i p q : ℤ) (h : (up ℤ).π (up ℤ) (up ℤ) (p, q) = i) :
    (singleStage I n).X p ⊗ F.X q ⟶ (productComplex I F n).X i :=
  if hp : p = 0 then
    eqToHom (congrArg (fun z ↦ (singleStage I n).X z ⊗ F.X q) hp) ≫
      eqToHom (congrArg (fun z ↦ (singleStage I n).X 0 ⊗ F.X z)
        (HomologicalComplex₂.ZeroColumn.index_eq hp h)) ≫ zeroTermMap I F n i
  else 0

/-- The ordinary tensor-complex comparison is assembled from the explicit
summand multiplication maps by the totalization coproduct. -/
def tensorComponent (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (n : ℕ) (i : ℤ) :
    (HomologicalComplex.tensorObj (singleStage I n) F).X i ⟶ (productComplex I F n).X i :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := singleStage I n) (K₂ := F) (F := curriedTensor X.Modules) (c := up ℤ)
    (A := (productComplex I F n).X i) (j := i) (summandMap I F n i)

/-- The actual chain map from tensor totalization to I^nF. -/
def tensorMap (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (n : ℕ) :
    HomologicalComplex.tensorObj (singleStage I n) F ⟶ productComplex I F n where
  f := tensorComponent I F n
  comm' := sorry

variable [DerivedTensor.Bifunctor.Has (C := X.Modules)]

/-- The actual derived tensor stage before multiplying into I^nF. -/
def sourceStage (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (n : ℕ) :
    DerivedCategory X.Modules :=
  (DerivedTensor.Bifunctor.rightFunctor (DerivedCategory.Q.obj F)).obj
    (DerivedCategory.Q.obj (singleStage I n))

/-- The specified derived tensor-to-ideal-product map: derived tensor counit,
then the localization of the explicit ordinary multiplication chain map. -/
def comparisonApp (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (n : ℕ) :
    sourceStage I F n ⟶ DerivedCategory.Q.obj (productComplex I F n) :=
  DerivedTensor.Bifunctor.counitAppOfQ (singleStage I n) F ≫
    DerivedCategory.Q.map (tensorMap I F n)

/-- The source positive system uses the actual ideal-power module transitions. -/
def sourceSystem (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) :
    PNatInverseSystem (DerivedCategory X.Modules) :=
  IdealPowerProduct.positiveSystem I (𝟙_ X.Modules) ⋙
    DerivedCategory.singleFunctor X.Modules 0 ⋙
      DerivedTensor.Bifunctor.rightFunctor (DerivedCategory.Q.obj F)

/-- The positive tensor comparison is the actual stage map at every index. -/
def comparison (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) :
    sourceSystem I F ⟶ positiveDerivedSystem I F where
  app n := comparisonApp I F ((OrderDual.ofDual n : ℕ+) : ℕ)
  naturality := sorry

/-- The same-power inclusion on ideal modules, obtained by factoring the
smaller filtration-stage arrow through the larger one. -/
def modulePowerInclusion {I I' : X.IdealSheafData} (h : I' ≤ I) (n : OrderDual ℕ+) :
    (IdealPowerProduct.positiveSystem I' (𝟙_ X.Modules)).obj n ⟶
      (IdealPowerProduct.positiveSystem I (𝟙_ X.Modules)).obj n :=
  ((IdealPowerFiltration.filtration I (𝟙_ X.Modules)).stage
      (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ)).factorThru
    ((IdealPowerFiltration.filtration I' (𝟙_ X.Modules)).stage
      (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ)).arrow
    (filtrationStage_factors h (𝟙_ X.Modules) (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ))

/-- The natural inclusion of the actual positive ideal-power module systems. -/
def moduleSystemInclusion {I I' : X.IdealSheafData} (h : I' ≤ I) :
    IdealPowerProduct.positiveSystem I' (𝟙_ X.Modules) ⟶
      IdealPowerProduct.positiveSystem I (𝟙_ X.Modules) where
  app := modulePowerInclusion h
  naturality := sorry

/-- The actual nested-ideal map on the derived tensor systems is obtained by
applying degree-zero localization and the fixed-right tensor functor. -/
def sourceInclusion {I I' : X.IdealSheafData} (h : I' ≤ I)
    (F : CochainComplex X.Modules ℤ) : sourceSystem I' F ⟶ sourceSystem I F :=
  Functor.whiskerRight (moduleSystemInclusion h)
    (DerivedCategory.singleFunctor X.Modules 0 ⋙
      DerivedTensor.Bifunctor.rightFunctor (DerivedCategory.Q.obj F))

/-- The specified tensor comparison is natural under the same-power ideal
inclusions. Neither the target map nor the square is a caller-supplied premise. -/
theorem comparison_idealInclusion {I I' : X.IdealSheafData} (h : I' ≤ I)
    (F : CochainComplex X.Modules ℤ) :
    sourceInclusion h F ≫ comparison I F =
      comparison I' F ≫ idealPowerSystemInclusion h F := sorry

/-- For a bounded termwise coherent complex on a Noetherian scheme, the
specified tensor-to-ideal-product map induces a pro-isomorphism. This is
the map of the affine algebra theorem glued over affine opens. -/
theorem comparison_isIso [IsNoetherian X] (I : X.IdealSheafData)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) :
    IsIso ((@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).map
      (comparison I F.obj)) := sorry

/-- The actual tensor-to-Deligne pro-isomorphism uses the specified
comparison map; its inverse is uniquely tied to that map. -/
def comparisonIso [IsNoetherian X] (I : X.IdealSheafData)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) :
    (@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).obj (sourceSystem I F.obj) ≅
      (@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).obj
        (positiveDerivedSystem I F.obj) :=
  @asIso _ _ _ _ ((@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).map
    (comparison I F.obj)) (comparison_isIso I F)

/-- The module-limit comparison induced by the actual tensor-to-product
pro-isomorphism. No pro-cohomology realization package is supplied. -/
def cohomologyComparisonIso {k : Type u} [Field k] [IsNoetherian X]
    (H : DerivedCategory X.Modules ⥤ ModuleCat.{u} k) (I : X.IdealSheafData)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) :
    limit (sourceSystem I F.obj ⋙ H) ≅ limit (positiveDerivedSystem I F.obj ⋙ H) :=
  Pro.ModuleLimit.mapIso H (comparisonIso I F)

/-- Realized tensor comparison is natural for nested ideals at the module-limit
level, with the actual two ideal-inclusion maps. -/
theorem cohomologyComparisonIso_naturality {k : Type u} [Field k] [IsNoetherian X]
    (H : DerivedCategory X.Modules ⥤ ModuleCat.{u} k) {I I' : X.IdealSheafData} (h : I' ≤ I)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) :
    limMap (Functor.whiskerRight (sourceInclusion h F.obj) H) ≫
        (cohomologyComparisonIso H I F).hom =
      (cohomologyComparisonIso H I' F).hom ≫
        limMap (Functor.whiskerRight (idealPowerSystemInclusion h F.obj) H) := sorry

/-- A bounded termwise coherent complex as its actual bounded coherent
derived object. Only boundedness/coherence membership is deferred. -/
def boundedObject [IsNoetherian X]
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] :=
  ⟨⟨DerivedCategory.Q.obj F.obj, sorry⟩, sorry⟩

/-- The actual map from the ideal-product complex to the original complex. -/
def productToOriginal (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ)
    (n : OrderDual ℕ+) :
    (positiveDerivedSystem I F).obj n ⟶ DerivedCategory.Q.obj F :=
  DerivedCategory.Q.map
    (HomologicalComplex.Filtered.Stage.inclusion (filtered I F)
      (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ))

/-- On the prescribed complement, the actual ideal-product inclusion
restricts to an isomorphism of derived complexes. -/
theorem productToOriginal_restriction_isIso {U : Scheme.{u}}
    (j : U ⟶ X) [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf))
    (n : OrderDual ℕ+) :
    IsIso ((RingedSpace.modulePullbackDerived j.toShHom).map
      (productToOriginal I F.obj n)) := sorry

/-- The constant restriction of the ideal-product system is constructed by
the actual stage inclusions and the canonical bounded-restriction comparison. -/
def productRestrictionIso {U : Scheme.{u}}
    (j : U ⟶ X) [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) :
    positiveDerivedSystem I F.obj ⋙ RingedSpace.modulePullbackDerived j.toShHom ≅
      (Functor.const (OrderDual ℕ+)).obj
        ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj
          ((restriction j).obj (boundedObject F))) :=
  NatIso.ofComponents
    (fun n ↦ @asIso _ _ _ _
        ((RingedSpace.modulePullbackDerived j.toShHom).map (productToOriginal I F.obj n))
        (productToOriginal_restriction_isIso j I hI F n) ≪≫
      (restrictionAmbientIso j).symm.app (boundedObject F))
    (fun _ ↦ sorry)

/-- The concrete Deligne presentation determined by I and F uses the
specified constant restriction, not an input comparison isomorphism. -/
def delignePresentation {U : Scheme.{u}}
    (j : U ⟶ X) [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) :
    DeligneSystem j where
  ideal := I
  complex := F
  openComplement_eq := hI
  value := (restriction j).obj (boundedObject F)
  restrictionIso := productRestrictionIso j I hI F

/-- The actual tensor comparison followed by the existing unique
restriction-normalized Deligne comparison gives the chosen extension owner. -/
def tensorToChosenExtensionIso {U : Scheme.{u}}
    (j : U ⟶ X) [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) :
    (@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).obj (sourceSystem I F.obj) ≅
      (extension j ((restriction j).obj (boundedObject F))).proObject :=
  comparisonIso I F ≪≫
    extensionIso j (delignePresentation j I hI F)
      ((restriction j).obj (boundedObject F)) (Iso.refl _)

/-- The specified tensor-to-chosen-extension comparison acts on cohomology
limits through the concrete represented-Hom realization. -/
def tensorToChosenExtensionCohomologyIso {k : Type u} [Field k] {U : Scheme.{u}}
    (j : U ⟶ X) [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]
    (H : DerivedCategory X.Modules ⥤ ModuleCat.{u} k)
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) :
    limit (sourceSystem I F.obj ⋙ H) ≅
      limit ((extension j ((restriction j).obj (boundedObject F))).tower ⋙ H) :=
  Pro.ModuleLimit.mapIso H (tensorToChosenExtensionIso j I hI F)

end AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.TensorComparison
