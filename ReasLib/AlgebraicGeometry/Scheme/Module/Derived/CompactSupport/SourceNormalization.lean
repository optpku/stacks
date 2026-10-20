/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.SourceExtension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.OpenDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.ChosenRealization
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived.KFlat
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
variable {k : Type u} [Field k] {X U : Scheme.{u}}
variable [IsNoetherian X] [IsNoetherian U]
variable [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [HomotopyTensorDescends U.toRingedSpace] [TensorDescends U.toRingedSpace]
variable [IsLocalization U.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived U.toRingedSpace)]
variable (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]
variable (j : U ⟶ X) [IsOpenImmersion j]

/-- Pull back the proper dual of the specified extension, use the canonical
monoidal pullback comparison, then precompose with the inverse of the actual
extension restriction isomorphism. -/
def sourceDualComparison (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (RingedSpace.modulePullbackDerived j.toShHom).obj
        ((ihom (sourceExtension j K).obj.obj).obj
          (Scheme.DerivedQCoh.properDualizingComplex q).obj) ⟶
      (ihom K.obj.obj).obj (openDualizing q j) :=
  -- Local instance justification (defeq pin): use the constructed opens-site monoidal pullback on the canonical K-flat categories; no monoidal datum is required from the caller.
  letI := RingedSpace.modulePullbackDerived.opensSiteMonoidal j.toShHom
  RingedSpace.modulePullbackDerived.InternalHom.comparison j.toShHom
      (sourceExtension j K).obj.obj (Scheme.DerivedQCoh.properDualizingComplex q).obj ≫
    (preIso (sourceExtensionAmbientIso j K)).hom.app (openDualizing q j)

/-- Open restriction preserves RHom out of the bounded coherent extension
into the bounded-below proper dualizing complex, so this specified map is invertible. -/
theorem sourceDualComparison_isIso (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    IsIso (sourceDualComparison q j K) := sorry

/-- The normalized source dual is obtained by inverting only the specified
restriction/RHom comparison, with the dualizing object literally Lj* q!O. -/
def sourceDualIso (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (RingedSpace.modulePullbackDerived j.toShHom).obj
        ((ihom (sourceExtension j K).obj.obj).obj
          (Scheme.DerivedQCoh.properDualizingComplex q).obj) ≅
      (ihom K.obj.obj).obj (openDualizing q j) :=
  @asIso _ _ _ _ (sourceDualComparison q j K) (sourceDualComparison_isIso q j K)

/-- The source-dual isomorphism retains exactly the specified comparison as its forward map. -/
theorem sourceDualIso_hom (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (sourceDualIso q j K).hom = sourceDualComparison q j K := rfl

/-- The source's bounded coherent dual has literally RHom(K,Lj* q!O)
as its ambient complex; boundedness and coherence are proof fields only. -/
def normalizedSourceDual (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf] :=
  ⟨⟨(ihom K.obj.obj).obj (openDualizing q j), sorry⟩, sorry⟩

/-- Restriction of the concrete coherent representative of the proper dual
identifies with the literal normalized source dual through the constructed maps. -/
def sourceRepresentativeIso (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (DeligneSystem.restriction j).obj (DeligneSystem.TensorComparison.boundedObject
        (IdealDuality.dualRepresentative q (sourceExtension j K))) ≅ normalizedSourceDual q j K :=
  (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).preimageIso
    ((DeligneSystem.restrictionAmbientIso j).app
        (DeligneSystem.TensorComparison.boundedObject
          (IdealDuality.dualRepresentative q (sourceExtension j K))) ≪≫
      (RingedSpace.modulePullbackDerived j.toShHom).mapIso
        (IdealDuality.dualRepresentativeIso q (sourceExtension j K)) ≪≫
      sourceDualIso q j K)

/-- The chosen compact-support extension of the representative identifies
with that of the literal normalized RHom source by functoriality. -/
def sourceCompactIso (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) (d : ℤ) :
    cohomology q (DeligneSystem.boundedTower j (DeligneSystem.extension j
      ((DeligneSystem.restriction j).obj (DeligneSystem.TensorComparison.boundedObject
        (IdealDuality.dualRepresentative q (sourceExtension j K)))))) d ≅
      cohomology q (DeligneSystem.boundedTower j (DeligneSystem.extension j
        (normalizedSourceDual q j K))) d :=
  Pro.ModuleLimit.mapIso (Cohomology.overFieldFunctor q d)
    ((DeligneSystem.extensionByZero j).mapIso (sourceRepresentativeIso q j K))

variable [DerivedCategory.DerivedTensor.Bifunctor.Has (C := RingedSpace.Modules X.toRingedSpace)]
variable [DerivedCategory.DerivedTensor.Bifunctor.Has (C := X.Modules)]

/-- The specified ideal complement and the original open immersion have the same range. -/
theorem sourceRange_eq (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) :
    Set.range j = Set.range I.openComplement.ι := sorry

/-- The canonical scheme isomorphism from the original source to the ideal complement. -/
def sourceRangeIso (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) :
    U ≅ I.openComplement.toScheme :=
  IsOpenImmersion.isoOfRangeEq j I.openComplement.ι (sourceRange_eq j I hI)

/-- The range isomorphism factors the original open immersion. -/
theorem sourceRangeIso_fac (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) :
    (sourceRangeIso j I hI).hom ≫ I.openComplement.ι = j :=
  IsOpenImmersion.isoOfRangeEq_hom_fac j I.openComplement.ι (sourceRange_eq j I hI)

/-- The range isomorphism respects the structural morphism to the field. -/
theorem sourceRangeIso_base (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) :
    (sourceRangeIso j I hI).hom ≫ (I.openComplement.ι ≫ q) = j ≫ q := sorry

/-- The ordinary source comparison is actual geometric restriction along
the canonical range isomorphism, followed by the chosen extension's restriction. -/
def sourceOrdinaryComparison (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) (i : ℤ) :
    IdealDuality.openOrdinary q I (IdealDuality.boundedInput (sourceExtension j K)) i ⟶
      (Cohomology.globalCohomologyOverField (j ≫ q) i).obj K.obj.obj :=
  let M := IdealDuality.boundedInput (sourceExtension j K)
  let g := (sourceRangeIso j I hI).hom
  IdealDuality.geometricOrdinaryRestriction (I.openComplement.ι ≫ q) g
      (IdealDuality.openInput I M) i ≫
    eqToHom (congrArg
      (fun p ↦ (Cohomology.globalCohomologyOverField p i).obj
        ((RingedSpace.modulePullbackDerived g.toShHom).obj (IdealDuality.openInput I M)))
      (sourceRangeIso_base q j I hI)) ≫
    (Cohomology.globalCohomologyOverField (j ≫ q) i).map
      ((IdealDuality.pullbackFactorizationIso g I.openComplement.ι j
        (sourceRangeIso_fac j I hI) M.obj).hom ≫ (sourceExtensionAmbientIso j K).hom)

/-- Restriction along the source-range isomorphism and the specified extension
comparison is invertible. -/
theorem sourceOrdinaryComparison_isIso (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) (i : ℤ) :
    IsIso (sourceOrdinaryComparison q j K I hI i) := sorry

/-- The ordinary comparison in the original source has its actual constructed forward map. -/
def sourceOrdinaryIso (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) (i : ℤ) :
    IdealDuality.openOrdinary q I (IdealDuality.boundedInput (sourceExtension j K)) i ≅
      (Cohomology.globalCohomologyOverField (j ≫ q) i).obj K.obj.obj :=
  @asIso _ _ _ _ (sourceOrdinaryComparison q j K I hI i)
    (sourceOrdinaryComparison_isIso q j K I hI i)

/-- The full proper-tensor/Deligne chain now lands in compact cohomology
of RHom(K,Lj* q!O), with the extension of K selected by the existing owner. -/
def normalizedSourceDuality (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) (i : ℤ) :
    Module.Dual k (IdealDuality.openOrdinary q I
      (IdealDuality.boundedInput (sourceExtension j K)) i) ≃ₗ[k]
      cohomology q (DeligneSystem.boundedTower j (DeligneSystem.extension j
        (normalizedSourceDual q j K))) (-i) :=
  (IdealDuality.normalizedChosenDuality q (sourceExtension j K) j I hI i).trans
    (sourceCompactIso q j K (-i)).toLinearEquiv

/-- On the original source, normalized duality has ordinary H^i(U,K) as its
left endpoint and compact cohomology of RHom(K,Lj* q!O) as its right endpoint. -/
def sourceDuality (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange) (i : ℤ) :
    Module.Dual k ((Cohomology.globalCohomologyOverField (j ≫ q) i).obj K.obj.obj) ≃ₗ[k]
      cohomology q (DeligneSystem.boundedTower j (DeligneSystem.extension j
        (normalizedSourceDual q j K))) (-i) :=
  (sourceOrdinaryIso q j K I hI i).toLinearEquiv.dualMap.trans
    (normalizedSourceDuality q j K I hI i)

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
