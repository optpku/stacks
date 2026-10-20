/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.TensorPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.CanonicalOpenRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Cohomology.ProperSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Cohomology

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
open DeligneSystem Cohomology
variable {k : Type u} [Field k] {X U U' : Scheme.{u}}
variable [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
variable (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]

/-- Proper sections compare the ambient and bounded coherent cohomology functors. -/
def boundedSectionsIso (d : ℤ) :
    ambient (SheafOfModules.isCoherent X.ringCatSheaf) ⋙ globalCohomologyOverField q d ≅
      overFieldFunctor q d :=
  NatIso.ofComponents
    (fun L ↦ properSectionsIso q
      ((Scheme.DerivedQCoh.coherentBoundedToDerivedQCoh X).obj L) d)
    (fun _ ↦ sorry)

/-- The canonical chosen Deligne extension has the actual bounded compact cohomology. -/
def chosenExtensionCohomologyIso (j : U ⟶ X) [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) (d : ℤ) :
    limit ((extension j K).tower ⋙ globalCohomologyOverField q d) ≅
      cohomology q (boundedTower j (extension j K)) d :=
  HasLimit.isoOfNatIso
    (Functor.isoWhiskerRight (boundedTowerAmbientIso j (extension j K)).symm
        (globalCohomologyOverField q d) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (boundedTower j (extension j K)) (boundedSectionsIso q d))

/-- Compact restriction is the module-limit realization of the specified geometric pro-map. -/
def chosenCompactRestriction (i : U' ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) (d : ℤ) :
    cohomology q (boundedTower (i ≫ j) (extension (i ≫ j) ((restriction i).obj K))) d ⟶
      cohomology q (boundedTower j (extension j K)) d :=
  Pro.ModuleLimit.map (overFieldFunctor q d) (canonicalOpenRestriction i j K)

/-- Tensor cohomology realizes as compact cohomology of the chosen Deligne extension. -/
def tensorToCompactIso
    [hTensor : DerivedCategory.DerivedTensor.Bifunctor.Has (C := X.Modules)]
    (j : U ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) (d : ℤ) :
    limit (TensorComparison.sourceSystem I F.obj ⋙ globalCohomologyOverField q d) ≅
      cohomology q (boundedTower j (extension j ((restriction j).obj
        (TensorComparison.boundedObject F)))) d :=
  (@TensorComparison.tensorToChosenExtensionCohomologyIso X hTensor k _ U j _ _ _
    (globalCohomologyOverField q d) I hI F) ≪≫
      chosenExtensionCohomologyIso q j ((restriction j).obj (TensorComparison.boundedObject F)) d

/-- Compact restriction for restrictions of a single bounded coherent object,
using the actual pullback compositor before the canonical geometric pro-map. -/
def chosenCompactRestrictionFromAmbient (i : U' ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) (d : ℤ) :
    cohomology q (boundedTower (i ≫ j) (extension (i ≫ j) ((restriction (i ≫ j)).obj L))) d ⟶
      cohomology q (boundedTower j (extension j ((restriction j).obj L))) d :=
  Pro.ModuleLimit.map (overFieldFunctor q d)
    ((extensionByZero (i ≫ j)).map ((restrictionCompIso i j).inv.app L) ≫
      canonicalOpenRestriction i j ((restriction j).obj L))

/-- The actual tensor ideal inclusions realize the canonical compact-support
open restriction under the specified Deligne and proper-sections comparisons. -/
theorem tensorToCompactIso_restriction
    [hTensor : DerivedCategory.DerivedTensor.Bifunctor.Has (C := X.Modules)]
    (i : U' ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j]
    {I I' : X.IdealSheafData} (h : I' ≤ I)
    (hI : I.openComplement = j.opensRange) (hI' : I'.openComplement = (i ≫ j).opensRange)
    (F : CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf)) (d : ℤ) :
    limMap (Functor.whiskerRight (TensorComparison.sourceInclusion h F.obj)
        (globalCohomologyOverField q d)) ≫ (tensorToCompactIso q j I hI F d).hom =
      (tensorToCompactIso q (i ≫ j) I' hI' F d).hom ≫
        chosenCompactRestrictionFromAmbient q i j (TensorComparison.boundedObject F) d := sorry

namespace IdealDuality
open RingedSpace.ModuleDerived.KFlat
variable [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [DerivedCategory.DerivedTensor.Bifunctor.Has (C := RingedSpace.Modules X.toRingedSpace)]
variable [hTensor : DerivedCategory.DerivedTensor.Bifunctor.Has (C := X.Modules)]

/-- The proper-duality tensor tower realizes as the chosen compact cohomology
of the restricted canonical representative of RHom(M,q!O). -/
def properTensorToCompactIso
    (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (j : U ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) (i : ℤ) :
    limit (compactDiagram q (boundedInput M) I i) ≅
      cohomology q (boundedTower j (extension j ((restriction j).obj
        (TensorComparison.boundedObject (dualRepresentative q M))))) (-i) :=
  (HasLimit.isoOfNatIso (sourceCohomologyIso q M I i)).symm ≪≫
    tensorToCompactIso q j I hI (dualRepresentative q M) (-i)

/-- The normalized proper-duality construction now lands in actual chosen
compact cohomology, rather than stopping at the tensor or product limit. -/
def normalizedChosenDuality
    (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (j : U ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) (i : ℤ) :
    Module.Dual k (openOrdinary q I (boundedInput M) i) ≃ₗ[k]
      cohomology q (boundedTower j (extension j ((restriction j).obj
        (TensorComparison.boundedObject (dualRepresentative q M))))) (-i) :=
  ((ordinaryColimitIso q (boundedInput M) (boundedInput_coherent M)
    (boundedInput_boundedBelow M) I i).toLinearEquiv.dualMap).trans
      ((dualityEquiv q (boundedInput M) (boundedInput_coherent M)
        (boundedInput_boundedBelow M) I i).trans
          (properTensorToCompactIso q M j I hI i).toLinearEquiv)

end IdealDuality
end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
