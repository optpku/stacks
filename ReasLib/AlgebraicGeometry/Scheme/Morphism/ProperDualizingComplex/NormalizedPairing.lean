/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Pairing
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.TensorComparison

/-!
# The unit-normalized proper trace pairing

The identification of the affine-derived field object with the ground field is
the inverse of the specified degree-zero derived-sections unit. No arbitrary
isomorphism of one-dimensional vector spaces is selected.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

/-- The degree-zero sections unit for a module sheaf, constructed from the
cochain-level unit of total right-derived global sections. -/
def globalSectionsToHomologyZero (X : Scheme.{u}) (M : X.Modules) :
    (RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace).obj M ⟶
      (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Scheme.globalSectionsRing X)) 0).obj
          ((RingedSpace.moduleDerivedGlobalSections X.toRingedSpace).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj M)) :=
  let F := RingedSpace.moduleGlobalSectionsFunctor X.toRingedSpace
  let d := DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app M) ≫
    (RingedSpace.Module.Derived.GlobalSections.unit X.toRingedSpace).app
      ((CochainComplex.singleFunctor X.Modules 0).obj M)
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} (Scheme.globalSectionsRing X)) 0).inv.app (F.obj M) ≫
    (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Scheme.globalSectionsRing X)) 0).map d

/-- The field maps to sections of its structure sheaf through `ΓSpecIso`.
The coefficient action is restriction along exactly that same ring map. -/
def fieldToStructureSections (k : Type u) [Field k] :
    ModuleCat.of k k ⟶
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).obj
        ((RingedSpace.moduleGlobalSectionsFunctor (Spec (CommRingCat.of k)).toRingedSpace).obj
          (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf)) :=
  let T : ModuleCat.{u} k :=
    (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).obj
      ((RingedSpace.moduleGlobalSectionsFunctor (Spec (CommRingCat.of k)).toRingedSpace).obj
        (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf))
  @ModuleCat.ofHom k _ k T _ _ T.isAddCommGroup T.isModule
    ({
      toFun := fun a ↦ (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a
      map_add' := sorry
      map_smul' := sorry } : k →ₗ[k] T)

/-- The canonical map from `k` to degree-zero affine derived sections of `O`.
It uses the actual sections unit and exact restriction of scalars. -/
def fieldObjectUnit (k : Type u) [Field k] : ModuleCat.of k k ⟶ fieldObject k :=
  let S : Scheme.{u} := Spec (CommRingCat.of k)
  let R : ModuleCat.{u} (Scheme.globalSectionsRing S) ⥤ ModuleCat.{u} k :=
    ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let M := SheafOfModules.unit S.ringCatSheaf
  fieldToStructureSections k ≫
    R.map (globalSectionsToHomologyZero S M) ≫
      (@exactFunctor_homology_iso_mapDerivedCategory
        (ModuleCat.{u} (Scheme.globalSectionsRing S)) (ModuleCat.{u} k)
        _ _ (ModuleCat.hasDerivedCategory (Scheme.globalSectionsRing S))
        _ _ (ModuleCat.hasDerivedCategory k) R _ _ _
        ((RingedSpace.moduleDerivedGlobalSections S.toRingedSpace).obj
          ((DerivedCategory.singleFunctor S.Modules 0).obj M)) 0).hom

/-- The specified degree-zero sections unit is invertible. -/
instance fieldObjectUnit_isIso (k : Type u) [Field k] : IsIso (fieldObjectUnit k) := sorry

/-- The canonical field identification, fixed by the sections unit. -/
def fieldObjectCanonicalIso (k : Type u) [Field k] : fieldObject k ≅ ModuleCat.of k k :=
  (asIso (fieldObjectUnit k)).symm

/-- The normalized field identification inverts the specified unit, fixing its
scale and hence the scale of the proper trace. -/
theorem fieldObjectCanonicalIso_unit (k : Type u) [Field k] :
    fieldObjectUnit k ≫ (fieldObjectCanonicalIso k).hom = 𝟙 (ModuleCat.of k k) := sorry

/-- The proper trace with the canonical ground-field normalization. -/
def normalizedTrace {k : Type u} [Field k] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q] :
    cohomologyOverField q (properDualizingComplex q) 0 ⟶ ModuleCat.of k k :=
  trace q ≫ (fieldObjectCanonicalIso k).hom

/-- The proper Ext/cohomology pairing with its scale fixed by the base unit. -/
def normalizedPairing {k : Type u} [Field k] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q] (i : ℤ) (L : DerivedQCoh X) :
    DerivedExt.value q L.obj (properDualizingComplex q).obj i →ₗ[k]
      Module.Dual k (cohomologyOverField q L (-i)) :=
  pairingWith (fieldObjectCanonicalIso k) q i L

/-- The normalized pairing is the named adjunction-based proper comparison,
followed by the fixed field identification. -/
theorem normalizedPairing_apply {k : Type u} [Field k] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q] (i : ℤ) (L : DerivedQCoh X)
    (α : DerivedExt.value q L.obj (properDualizingComplex q).obj i) :
    normalizedPairing q i L α =
      (extComparison q i L (ambientExtLift q i L α) ≫
        (fieldObjectCanonicalIso k).hom).hom := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

namespace AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

open RingedSpace.ModuleDerived.KFlat CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]

/-- The ordinary RHom stage is quasicoherent for the source's coherent
bounded-above ideal stage and bounded-below extension complex. -/
theorem ordinaryStage_mem (I M : DerivedQCoh X)
    (hI : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) I.obj)
    (hIa : (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) I.obj)
    (hM : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) M.obj)
    (hMb : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) M.obj) :
    ModuleDerived.quasicoherentProperty X ((ihom I.obj).obj M.obj) := sorry

/-- The actual ordinary stage `RHom(I,M)`, with only its quasicoherence
certificate deferred. No arbitrary stage object or isomorphism is chosen. -/
def ordinaryStage (I M : DerivedQCoh X)
    (hI : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) I.obj)
    (hIa : (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) I.obj)
    (hM : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) M.obj)
    (hMb : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) M.obj) :
    DerivedQCoh X :=
  ⟨(ihom I.obj).obj M.obj, ordinaryStage_mem I M hI hIa hM hMb⟩

end AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

namespace AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

open RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalClosed

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]
variable [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [HomotopyTensorDescends (Spec (CommRingCat.of k)).toRingedSpace]
variable [TensorDescends (Spec (CommRingCat.of k)).toRingedSpace]
variable [IsLocalization (Spec (CommRingCat.of k)).toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom q.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived q.toShHom)]

/-- The sheafy proper trace uses the actual chosen pushforward adjunction and
its counit at the base structure sheaf. There is no free object comparison. -/
def normalizedSheafyTrace (L : DerivedQCoh X) :=
  -- Local instance justification (search instability): compactness is derived from the supplied proper morphism q, which cannot be recovered from X by instance search.
  letI := QuasiCompact.compactSpace_of_compactSpace q
  -- Local instance justification (search instability): quasi-separatedness is derived from q and cannot infer this chosen structural morphism from X.
  letI := quasiSeparatedSpace_of_quasiSeparated q
  uncoheratedSheafyTraceMap q (pushforwardCohomologyIn q).rightAdjoint
    (Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn q)) L
    (structureSheaf (Spec (CommRingCat.of k)))

/-- Ground-field-valued cohomology on the base spectrum, retaining the explicit
affine scalar restriction even for ambient derived objects. -/
def baseCohomologyFunctor (k : Type u) [Field k] (i : ℤ) :
    RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace ⥤ ModuleCat.{u} k :=
  RingedSpace.moduleDerivedGlobalSections (Spec (CommRingCat.of k)).toRingedSpace ⋙
    ModuleCat.derivedRestrictionOfScalars (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) i

/-- The actual ground-field-linear map on degree-`i` cohomology of the sheafy
proper trace. Its source is the pushforward of `RHom(L,q!O)` and its target
is `RHom(Rq_*L,O)`; the subsequent RHom-to-Ext comparison is separate. -/
def normalizedSheafyTraceCohomology (L : DerivedQCoh X) (i : ℤ) :=
  (baseCohomologyFunctor k i).map (normalizedSheafyTrace q L)

/-- A specified right-adjoint model is compared by uniqueness of right
adjoints, so its trace normalization is tied to its adjunction counit. -/
def specifiedAdjointComparison
    (a : DerivedQCoh (Spec (CommRingCat.of k)) ⥤ DerivedQCoh X)
    (adj : pushforwardCohomologyIn q ⊣ a) :
    properDualizingComplex q ≅ a.obj (structureSheaf (Spec (CommRingCat.of k))) :=
  isoOfAdjunction q a adj

/-- The sheafy trace formed from a specified adjunction is the normalized
trace after the unique comparison of the two right adjoints. -/
theorem normalizedSheafyTrace_specifiedAdjoint
    (a : DerivedQCoh (Spec (CommRingCat.of k)) ⥤ DerivedQCoh X)
    (adj : pushforwardCohomologyIn q ⊣ a) (L : DerivedQCoh X) :
    -- Local instance justification (search instability): the proper source's compactness follows from q, not from a globally inferable choice of structural morphism.
    letI := QuasiCompact.compactSpace_of_compactSpace q
    -- Local instance justification (search instability): derive quasi-separatedness from this specified proper morphism for the sheafy comparison.
    letI := quasiSeparatedSpace_of_quasiSeparated q
    (RingedSpace.moduleDerivedPushforward q.toShHom).map
        ((ihom L.obj).map
          ((inclusion X).map (specifiedAdjointComparison q a adj).hom)) ≫
      uncoheratedSheafyTraceMap q a adj L
        (structureSheaf (Spec (CommRingCat.of k))) =
      normalizedSheafyTrace q L := sorry

open DerivedCategory.TStructure

/-- The concrete stage arrow for the compact-support duality argument:
push forward the tensor–RHom comparison, then apply the counit-normalized
proper sheafy trace to `RHom(I,M)`. It is defined before any homology is taken. -/
def tensorStageTrace [IsLocallyNoetherian X] (I M : DerivedQCoh X)
    (hI : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) I.obj)
    (hIa : (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) I.obj)
    (hM : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) M.obj)
    (hMb : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) M.obj) :=
  (RingedSpace.moduleDerivedPushforward q.toShHom).map
      (TensorRight.comparisonOf
        (inferInstance : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
        I.obj M.obj (properDualizingComplex q).obj) ≫
    normalizedSheafyTrace q (ordinaryStage I M hI hIa hM hMb)

/-- The actual linear cohomology map of the tensor-stage proper trace.
For the source's pairing use degree `-i`; no boundedness of the tensor
stage itself is asserted. -/
def tensorStageTraceCohomology [IsLocallyNoetherian X] (I M : DerivedQCoh X)
    (hI : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) I.obj)
    (hIa : (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) I.obj)
    (hM : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.ringCatSheaf) M.obj)
    (hMb : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) M.obj)
    (i : ℤ) :=
  (baseCohomologyFunctor k i).map (tensorStageTrace q I M hI hIa hM hMb)

end AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
