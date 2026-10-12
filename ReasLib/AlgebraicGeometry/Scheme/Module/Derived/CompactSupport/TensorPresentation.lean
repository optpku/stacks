/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.TensorComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Representative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.OrdinaryColimit
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Duality
public import ReasLib.CategoryTheory.Filtration.ZeroObject

/-! Canonical links between the proper dual tensor tower and its bounded
termwise-coherent Deligne presentation. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived.KFlat Scheme.Modules
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.IdealDuality

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsNoetherian X]
variable [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]

-- Local instance justification (defeq pin): sourceSystem exposes D(X.Modules), whereas the canonical K-flat instance is indexed by the definitionally equal ringed-space presentation; pin that exact canonical structure.
local instance schemeDerivedMonoidal : MonoidalCategory (DerivedCategory X.Modules) :=
  RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace

-- Local instance justification (defeq pin): use the same K-flat symmetry for braiding the scheme-module tensor stages; this adds no alternate tensor data.
local instance schemeDerivedSymmetric : SymmetricCategory (DerivedCategory X.Modules) :=
  RingedSpace.ModuleDerived.symmetricCategory X.toRingedSpace

/-- The actual filtered degree-zero ideal stage is identified with the
single ideal module used by the tensor comparison through functorial
single-complex comparisons and the structure-sheaf tensor-unit map. -/
def idealStageSingleIso (I : X.IdealSheafData) (n : OrderDual ℕ+) :
    (idealStage I n).obj ≅ DerivedCategory.Q.obj
      (DeligneSystem.TensorComparison.singleStage I ((OrderDual.ofDual n : ℕ+) : ℕ)) :=
  let F := IdealPowerFiltration.filtered I
  let G : FilteredObject (RingedSpace.Modules X.toRingedSpace) ⥤ (RingedSpace.Modules X.toRingedSpace) :=
    FilteredObject.Stage.functor (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ)
  DerivedCategory.Q.mapIso
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app
          (SheafOfModules.unit X.ringCatSheaf)) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).app
        (F.obj (SheafOfModules.unit X.ringCatSheaf)) ≪≫
      (CochainComplex.singleFunctor (RingedSpace.Modules X.toRingedSpace) 0).mapIso
        ((F ⋙ G).mapIso (RingedSpace.unitIsoTensorUnit X.toRingedSpace)))

variable (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]

/-- The actual bounded coherent dual of M under the proper adjunction's q!O. -/
def properDualObject (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] :=
  -- Local instance justification (search instability): compactness is derived from this proper structural morphism q and cannot be inferred from X alone.
  letI := QuasiCompact.compactSpace_of_compactSpace q
  (Scheme.IsDualizingComplex.boundedDuality HX
    (Scheme.DerivedQCoh.properDualizingComplex q).obj
    (Scheme.DerivedQCoh.ProperDualizingComplex.isDualizing q)).obj (op M)

/-- The bounded coherent representative of the actual proper dual. -/
def dualRepresentative (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf) :=
  CoherentRepresentative.complex X (properDualObject q M)

/-- The specified representative comparison identifies QF with RHom(M,q!O). -/
def dualRepresentativeIso (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    DerivedCategory.Q.obj (dualRepresentative q M).obj ≅
      (ihom M.obj.obj).obj (Scheme.DerivedQCoh.properDualizingComplex q).obj :=
  -- Local instance justification (search instability): the bounded-duality object computation uses the compactness supplied by q.
  letI := QuasiCompact.compactSpace_of_compactSpace q
  CoherentRepresentative.comparisonIso X (properDualObject q M) ≪≫
    eqToIso (Scheme.IsDualizingComplex.boundedDuality_obj_obj_obj HX
      (Scheme.DerivedQCoh.properDualizingComplex q).obj
      (Scheme.DerivedQCoh.ProperDualizingComplex.isDualizing q) (op M))

variable [DerivedCategory.DerivedTensor.Bifunctor.Has (C := (RingedSpace.Modules X.toRingedSpace))]

/-- The chosen coherent representative's derived tensor stage is identified
with the actual duality tensor stage by the canonical tensor model,
symmetry, representative comparison and ideal-stage comparison. -/
def sourceStageIso (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (I : X.IdealSheafData) (n : OrderDual ℕ+) :
    (@DeligneSystem.TensorComparison.sourceSystem X
      (inferInstanceAs (DerivedCategory.DerivedTensor.Bifunctor.Has
        (C := RingedSpace.Modules X.toRingedSpace))) I (dualRepresentative q M).obj).obj n ≅
      ((ihom M.obj.obj).obj (Scheme.DerivedQCoh.properDualizingComplex q).obj) ⊗
        (idealStage I n).obj :=
  let A : RingedSpace.ModuleDerived X.toRingedSpace := DerivedCategory.Q.obj
    (DeligneSystem.TensorComparison.singleStage I ((OrderDual.ofDual n : ℕ+) : ℕ))
  let B : RingedSpace.ModuleDerived X.toRingedSpace := DerivedCategory.Q.obj (dualRepresentative q M).obj
  let model := @Scheme.ModuleDerived.ProjectionFormula.kFlatTensorModel X
    (Scheme.ModuleDerived.ProjectionFormula.hasKFlatResolutions X)
    (inferInstanceAs (HomotopyTensorDescends X.toRingedSpace))
    (inferInstanceAs (TensorDescends X.toRingedSpace))
    (inferInstanceAs (TensorDescends X.toRingedSpace))
    (inferInstanceAs (IsLocalization X.toRingedSpace))
    (inferInstanceAs (IsLocalization X.toRingedSpace))
    (Scheme.ModuleDerived.ProjectionFormula.homotopyLocalization_isLocalization X)
  (DerivedCategory.DerivedTensor.Bifunctor.Right.isoApp B A).symm ≪≫
    (@DerivedCategory.DerivedTensor.Right.Monoidal.Model.objIsoTensor
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace)
      model A B _) ≪≫
    (@BraidedCategory.braiding (RingedSpace.ModuleDerived X.toRingedSpace) _
      (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace)
      (RingedSpace.ModuleDerived.symmetricCategory X.toRingedSpace).toBraidedCategory A B) ≪≫
    tensorIso (dualRepresentativeIso q M) (idealStageSingleIso I n).symm

open DerivedCategory.TStructure Scheme.ModuleDerived.Cohomology

/-- The original bounded coherent input in the quasicoherent presentation. -/
abbrev boundedInput (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) : Scheme.DerivedQCoh X :=
  (Scheme.DerivedQCoh.coherentBoundedToDerivedQCoh X).obj M

/-- The included bounded coherent input retains coherent cohomology. -/
theorem boundedInput_coherent (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    DerivedCategory.cohomologyIn (SheafOfModules.isCoherent X.ringCatSheaf)
      (boundedInput M).obj := sorry

/-- The included bounded coherent input is bounded below. -/
theorem boundedInput_boundedBelow (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))
      (boundedInput M).obj := sorry

variable [hTensorScheme : DerivedCategory.DerivedTensor.Bifunctor.Has (C := X.Modules)]

/-- The actual tensor-model comparison applied stagewise to cohomology. -/
def sourceCohomologyIso (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (I : X.IdealSheafData) (i : ℤ) :
    DeligneSystem.TensorComparison.sourceSystem I (dualRepresentative q M).obj ⋙
        globalCohomologyOverField q (-i) ≅ compactDiagram q (boundedInput M) I i :=
  NatIso.ofComponents
    (fun n ↦ (globalCohomologyOverField q (-i)).mapIso (sourceStageIso q M I n))
    (fun _ ↦ sorry)

/-- Compact cohomology in the canonical bounded Deligne-product model of
the fixed proper dual, using the selected bounded coherent representative. -/
abbrev deligneCompactCohomology (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (I : X.IdealSheafData) (i : ℤ) : ModuleCat.{u} k :=
  limit (Scheme.Modules.IdealPowerComplex.positiveDerivedSystem I
    (dualRepresentative q M).obj ⋙ globalCohomologyOverField q (-i))

/-- The tensor cohomology limit is identified with the bounded Deligne
cohomology limit by the specified tensor comparison and its realized inverse. -/
def throughLimitIso {k : Type u} [Field k]
    {A B : PNatInverseSystem (ModuleCat.{u} k)} {T : ModuleCat.{u} k}
    (e : A ≅ B) (f : limit A ≅ T) : limit B ≅ T :=
  (HasLimit.isoOfNatIso e).symm ≪≫ f

/-- The concrete tensor/Deligne limit comparison uses only the two specified component maps. -/
def tensorToDeligneLimitIso (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (I : X.IdealSheafData) (i : ℤ) :
    limit (compactDiagram q (boundedInput M) I i) ≅ deligneCompactCohomology q M I i :=
  throughLimitIso (sourceCohomologyIso q M I i)
    (@DeligneSystem.TensorComparison.cohomologyComparisonIso X hTensorScheme k _ _
      (globalCohomologyOverField q (-i)) I (dualRepresentative q M))

/-- The Deligne compact-support map is induced directly by the same-power
ideal inclusions, independently of the horizontal duality map. -/
def deligneCompactRestriction (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    {I I' : X.IdealSheafData} (h : I' ≤ I) (i : ℤ) :
    deligneCompactCohomology q M I' i ⟶ deligneCompactCohomology q M I i :=
  limMap (Functor.whiskerRight
    (Scheme.Modules.IdealPowerComplex.idealPowerSystemInclusion h (dualRepresentative q M).obj)
    (globalCohomologyOverField q (-i)))

/-- The constructed tensor/Deligne identification is natural in the actual
ideal-inclusion maps. -/
theorem tensorToDeligneLimitIso_naturality
    (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    {I I' : X.IdealSheafData} (h : I' ≤ I) (i : ℤ) :
    limMap (compactRestriction q (boundedInput M) h i) ≫ (tensorToDeligneLimitIso q M I i).hom =
      (tensorToDeligneLimitIso q M I' i).hom ≫ deligneCompactRestriction q M h i := sorry

/-- The normalized geometric ordinary-dual to Deligne compact-cohomology
comparison in the source's common proper compactification. -/
def geometricDualityEquiv (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (I : X.IdealSheafData) (i : ℤ) :
    Module.Dual k (openOrdinary q I (boundedInput M) i) ≃ₗ[k] deligneCompactCohomology q M I i :=
  (ordinaryColimitIso q (boundedInput M) (boundedInput_coherent M)
      (boundedInput_boundedBelow M) I i).toLinearEquiv.dualMap |>.trans
    ((dualityEquiv q (boundedInput M) (boundedInput_coherent M)
      (boundedInput_boundedBelow M) I i).trans (tensorToDeligneLimitIso q M I i).toLinearEquiv)

/-- The full source-direction square in the common proper compactification
commutes for the independently constructed ordinary and compact maps. -/
theorem geometricDuality_openRestriction
    (M : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    {I I' : X.IdealSheafData} (h : I' ≤ I) (i : ℤ) :
    (deligneCompactRestriction q M h i).hom.comp (geometricDualityEquiv q M I' i).toLinearMap =
      (geometricDualityEquiv q M I i).toLinearMap.comp
        (openRestrictionFromIdeals q h (boundedInput M) i).hom.dualMap := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.IdealDuality
