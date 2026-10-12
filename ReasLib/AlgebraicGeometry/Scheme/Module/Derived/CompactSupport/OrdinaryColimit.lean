/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.IdealPowerDuality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Cohomology.ProperSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.PlusModel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal

/-!
# The geometric ordinary-colimit comparison on an ideal complement

The constant restriction of I^n O_X is obtained by inverting its specified
inclusion after pullback. Stage classes are restricted through that map and
the derived pullback unit comparison, preserving the ground-field action.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived.KFlat Scheme.Hom DerivedCategory.TStructure
open Scheme.DerivedQCoh.ProperDualizingComplex Scheme.ModuleDerived.Cohomology
open Scheme.Modules.IdealPowerComplex

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.IdealDuality

/-- The ground-field map of a composite structural morphism is the actual
restriction of the ground-field map on the larger scheme. -/
theorem sectionScalars_comp {k : Type u} [Field k] {U U' : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of k)) (j : U' ⟶ U) :
    (j ≫ p).globalSectionsMap = j.appTop.hom.comp p.globalSectionsMap := sorry

/-- The geometric derived restriction over the ground field, constructed
from the pullback/pushforward adjunction unit and the actual sections
pushforward comparison. It is independent of any ideal-power presentation. -/
def geometricDerivedRestriction {k : Type u} [Field k] {U U' : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of k)) (j : U' ⟶ U)
    (E : RingedSpace.ModuleDerived U.toRingedSpace) :
    (ModuleCat.derivedRestrictionOfScalars p.globalSectionsMap).obj
        ((RingedSpace.moduleDerivedGlobalSections U.toRingedSpace).obj E) ⟶
      (ModuleCat.derivedRestrictionOfScalars (j ≫ p).globalSectionsMap).obj
        ((RingedSpace.moduleDerivedGlobalSections U'.toRingedSpace).obj
          ((RingedSpace.modulePullbackDerived j.toShHom).obj E)) :=
  -- Local instance justification (proof-local temporary data): the canonical derived adjunction requires its HasPair witness for this specified geometric morphism.
  letI := Scheme.DerivedQCoh.pullbackPushforwardAdjunctionHasPair j
  (ModuleCat.derivedRestrictionOfScalars p.globalSectionsMap).map
      (RingedSpace.Module.Derived.GlobalSections.mapOfPushforward j.toShHom
        ((RingedSpace.modulePullbackDerivedPushforwardAdjunction j.toShHom).unit.app E)) ≫
    (ModuleCat.DerivedRestriction.compObjIsoOfEq p.globalSectionsMap j.appTop.hom
      (j ≫ p).globalSectionsMap (sectionScalars_comp p j)
      ((RingedSpace.moduleDerivedGlobalSections U'.toRingedSpace).obj
        ((RingedSpace.modulePullbackDerived j.toShHom).obj E))).inv

/-- The ordinary geometric restriction in degree i is the homology of the
specified derived restriction, hence a genuine ground-field-linear map. -/
def geometricOrdinaryRestriction {k : Type u} [Field k] {U U' : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of k)) (j : U' ⟶ U)
    (E : RingedSpace.ModuleDerived U.toRingedSpace) (i : ℤ) :
    (globalCohomologyOverField p i).obj E ⟶
      (globalCohomologyOverField (j ≫ p) i).obj
        ((RingedSpace.modulePullbackDerived j.toShHom).obj E) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).map
    (geometricDerivedRestriction p j E)

/-- Underived pullback carries the structure sheaf to the structure sheaf
through its canonical strong-monoidal core. -/
def openStructureUnitIso {X U : Scheme.{u}} (j : U ⟶ X) :
    (RingedSpace.Hom.pullback j.toShHom).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit U.ringCatSheaf :=
  (RingedSpace.Hom.pullback j.toShHom).mapIso
      (RingedSpace.unitIsoTensorUnit X.toRingedSpace) ≪≫
    RingedSpace.Hom.pullbackUnitIsoOf j.toShHom
      (RingedSpace.Hom.presheafCoreMonoidal j.toShHom) ≪≫
    (RingedSpace.unitIsoTensorUnit U.toRingedSpace).symm

/-- The derived unit comparison for an open immersion is constructed from
the exact-pullback comparison and the actual underived unit map. -/
def openDerivedUnitIso {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (RingedSpace.modulePullbackDerived j.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor U.Modules 0).obj (SheafOfModules.unit U.ringCatSheaf) :=
  let F := (Scheme.DerivedQCoh.OpenImmersion.exactPullback j).obj
  let O := SheafOfModules.unit X.ringCatSheaf
  (Scheme.DerivedQCoh.OpenImmersion.exactPullbackIso j).symm.app
      ((DerivedCategory.singleFunctor X.Modules 0).obj O) ≪≫
    F.mapDerivedCategoryFactors.app ((CochainComplex.singleFunctor X.Modules 0).obj O) ≪≫
    DerivedCategory.Q.mapIso ((F.mapCochainComplexSingleFunctor 0).app O) ≪≫
    (DerivedCategory.singleFunctor U.Modules 0).mapIso (openStructureUnitIso j)

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsNoetherian X]
variable [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]

/-- The ideal-power stage's actual inclusion into O_X[0]. -/
def idealToUnit (I : X.IdealSheafData) (n : OrderDual ℕ+) :
    (idealStage I n).obj ⟶ DerivedCategory.Q.obj unitComplex :=
  DerivedCategory.Q.map
    (HomologicalComplex.Filtered.Stage.inclusion (filtered I unitComplex)
      (((OrderDual.ofDual n : ℕ+) : ℕ) : ℤ))

/-- On the ideal complement the specified ideal-power inclusion is invertible. -/
instance restrictedIdealToUnit_isIso (I : X.IdealSheafData) (n : OrderDual ℕ+) :
    IsIso ((RingedSpace.modulePullbackDerived I.openComplement.ι.toShHom).map
      (idealToUnit I n)) := sorry

/-- The restricted ideal-stage is identified with O_U[0] by the actual
restricted inclusion followed by the canonical derived unit map. -/
def restrictedIdealUnitIso (I : X.IdealSheafData) (n : OrderDual ℕ+) :
    (RingedSpace.modulePullbackDerived I.openComplement.ι.toShHom).obj (idealStage I n).obj ≅
      (DerivedCategory.singleFunctor I.openComplement.toScheme.Modules 0).obj
        (SheafOfModules.unit I.openComplement.toScheme.ringCatSheaf) :=
  asIso ((RingedSpace.modulePullbackDerived I.openComplement.ι.toShHom).map (idealToUnit I n)) ≪≫
    openDerivedUnitIso I.openComplement.ι

/-- The restricted input complex, using the actual derived open pullback. -/
def openInput (I : X.IdealSheafData) (M : Scheme.DerivedQCoh X) :
    RingedSpace.ModuleDerived I.openComplement.toScheme.toRingedSpace :=
  (RingedSpace.modulePullbackDerived I.openComplement.ι.toShHom).obj M.obj

/-- The ordinary cohomology object on the geometric ideal complement. -/
def openOrdinary (q : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (M : Scheme.DerivedQCoh X) (i : ℤ) : ModuleCat.{u} k :=
  (globalCohomologyOverField (I.openComplement.ι ≫ q) i).obj (openInput I M)

/-- Inclusion of ideals gives inclusion of their open complements in the same direction. -/
theorem idealComplement_le {I I' : X.IdealSheafData} (h : I' ≤ I) :
    I'.openComplement ≤ I.openComplement := sorry

/-- The actual inclusion between the two ideal complements. -/
def idealOpenInclusion {I I' : X.IdealSheafData} (h : I' ≤ I) :
    I'.openComplement.toScheme ⟶ I.openComplement.toScheme :=
  X.homOfLE (idealComplement_le h)

/-- The nested-open inclusion has the prescribed composite in the ambient scheme. -/
theorem idealOpenInclusion_comp {I I' : X.IdealSheafData} (h : I' ≤ I) :
    idealOpenInclusion h ≫ I.openComplement.ι = I'.openComplement.ι :=
  X.homOfLE_ι (idealComplement_le h)

/-- The nested-open structural map agrees with the smaller open's structural map. -/
theorem idealOpenInclusion_base (q : X ⟶ Spec (CommRingCat.of k))
    {I I' : X.IdealSheafData} (h : I' ≤ I) :
    idealOpenInclusion h ≫ (I.openComplement.ι ≫ q) = I'.openComplement.ι ≫ q := sorry

/-- Iterated restriction of the input complex is identified with restriction
to the smaller open by the specified derived-pullback compositor. -/
def pullbackFactorizationIso {A B C : Scheme.{u}}
    (i : A ⟶ B) (j : B ⟶ C) (f : A ⟶ C) (hf : i ≫ j = f)
    (E : RingedSpace.ModuleDerived C.toRingedSpace) :
    (RingedSpace.modulePullbackDerived i.toShHom).obj
        ((RingedSpace.modulePullbackDerived j.toShHom).obj E) ≅
      (RingedSpace.modulePullbackDerived f.toShHom).obj E :=
  hf ▸ (RingedSpace.modulePullbackDerived.compIso i.toShHom j.toShHom
    (RingedSpace.modulePullbackDerived.compComparison_isIso i.toShHom j.toShHom)).app E

/-- The concrete ideal-open specialization of the canonical factorization comparison. -/
def openInputRestrictionIso {I I' : X.IdealSheafData} (h : I' ≤ I)
    (M : Scheme.DerivedQCoh X) :
    (RingedSpace.modulePullbackDerived (idealOpenInclusion h).toShHom).obj (openInput I M) ≅
      openInput I' M :=
  pullbackFactorizationIso (idealOpenInclusion h) I.openComplement.ι I'.openComplement.ι
    (idealOpenInclusion_comp h) M.obj

/-- Ordinary geometric restriction between ideal complements is induced by
the derived adjunction unit, followed only by the actual structural-map and
pullback-composition identifications. It is not defined through the colimit. -/
def openRestrictionFromIdeals (q : X ⟶ Spec (CommRingCat.of k))
    {I I' : X.IdealSheafData} (h : I' ≤ I) (M : Scheme.DerivedQCoh X) (i : ℤ) :
    openOrdinary q I M i ⟶ openOrdinary q I' M i :=
  geometricOrdinaryRestriction (I.openComplement.ι ≫ q) (idealOpenInclusion h)
      (openInput I M) i ≫
    eqToHom (congrArg
      (fun p ↦ (globalCohomologyOverField p i).obj
        ((RingedSpace.modulePullbackDerived (idealOpenInclusion h).toShHom).obj (openInput I M)))
      (idealOpenInclusion_base q h)) ≫
    (globalCohomologyOverField (I'.openComplement.ι ≫ q) i).map
      (openInputRestrictionIso h M).hom

/-- Restrict an actual Ext class from I^n to O_U via the specified inclusion
inverse, then take derived sections and the degree conversion. -/
def restrictedExtClass (q : X ⟶ Spec (CommRingCat.of k))
    (I : X.IdealSheafData) (M : Scheme.DerivedQCoh X) (i : ℤ) (n : OrderDual ℕ+)
    (α : DerivedExt.value q (idealStage I n).obj M.obj i) : openOrdinary q I M i :=
  let P := RingedSpace.modulePullbackDerived I.openComplement.ι.toShHom
  let p := I.openComplement.ι ≫ q
  -- Local instance justification (defeq pin): use the shift transported through the canonical exact-open-pullback comparison for this restriction map.
  letI := Functor.CommShift.ofIso
    (Scheme.DerivedQCoh.OpenImmersion.exactPullbackIso I.openComplement.ι) ℤ
  let f := (restrictedIdealUnitIso I n).inv ≫ P.map α ≫ (P.commShiftIso i).hom.app M.obj
  (globalDegreeIso p (openInput I M) i).hom.hom
    (((groundFieldToDerivedSections p) ≫ (globalCohomologyOverField p 0).map f).hom 1)

variable (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]
variable (M : Scheme.DerivedQCoh X)
variable (hM : DerivedCategory.cohomologyIn (SheafOfModules.isCoherent X.ringCatSheaf) M.obj)
variable (hMb : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) M.obj)

/-- The stage-to-open comparison converts the actual proper cohomology stage
to Ext and restricts that class through the canonical geometric map. -/
def ordinaryStageToOpenFun (I : X.IdealSheafData) (i : ℤ) (n : ℕ+)
    (x : (ordinaryDiagram q M hM hMb I i).obj n) : openOrdinary q I M i :=
  let L := ordinaryStage (idealStage I n) M (idealStage_coherent I n)
    (idealStage_boundedAbove I n) hM hMb
  restrictedExtClass q I M i n
    (rhomCohomologyExtEquiv q (idealStage I n).obj M.obj i
      ((properSectionsIso q L i).inv.hom x))

/-- Additivity of the specified stage restriction follows from its actual maps. -/
theorem ordinaryStageToOpenFun_add (I : X.IdealSheafData) (i : ℤ) (n : ℕ+)
    (x y : (ordinaryDiagram q M hM hMb I i).obj n) :
    ordinaryStageToOpenFun q M hM hMb I i n (x + y) =
      ordinaryStageToOpenFun q M hM hMb I i n x +
        ordinaryStageToOpenFun q M hM hMb I i n y := sorry

/-- The stage restriction respects scalars because pullback is over the
specified ground-field structure morphism, with no additive transport choice. -/
theorem ordinaryStageToOpenFun_smul (I : X.IdealSheafData) (i : ℤ) (n : ℕ+)
    (a : k) (x : (ordinaryDiagram q M hM hMb I i).obj n) :
    ordinaryStageToOpenFun q M hM hMb I i n (a • x) =
      a • ordinaryStageToOpenFun q M hM hMb I i n x := sorry

/-- The actual stage restriction as a ground-field-linear map. -/
def ordinaryStageToOpen (I : X.IdealSheafData) (i : ℤ) (n : ℕ+) :
    (ordinaryDiagram q M hM hMb I i).obj n ⟶ openOrdinary q I M i :=
  ModuleCat.ofHom
    { toFun := ordinaryStageToOpenFun q M hM hMb I i n
      map_add' := ordinaryStageToOpenFun_add q M hM hMb I i n
      map_smul' := ordinaryStageToOpenFun_smul q M hM hMb I i n }

/-- The specified maps define the geometric ordinary-cohomology cocone. -/
def ordinaryOpenCocone (I : X.IdealSheafData) (i : ℤ) :
    Cocone (ordinaryDiagram q M hM hMb I i) where
  pt := openOrdinary q I M i
  ι := { app := ordinaryStageToOpen q M hM hMb I i, naturality := sorry }

/-- The canonical ordinary-colimit map is the descendent of the actual
geometric stage restriction cocone. -/
def ordinaryColimitToOpen (I : X.IdealSheafData) (i : ℤ) :
    colimit (ordinaryDiagram q M hM hMb I i) ⟶ openOrdinary q I M i :=
  colimit.desc _ (ordinaryOpenCocone q M hM hMb I i)

/-- The actual colimit comparison is invertible by the coherent ideal-power
restriction theorem on the Noetherian open complement. -/
instance ordinaryColimitToOpen_isIso (I : X.IdealSheafData) (i : ℤ) :
    IsIso (ordinaryColimitToOpen q M hM hMb I i) := sorry

/-- The geometric ordinary-colimit identification is the isomorphism of the
specified colimit map, not a separately chosen cohomology isomorphism. -/
def ordinaryColimitIso (I : X.IdealSheafData) (i : ℤ) :
    colimit (ordinaryDiagram q M hM hMb I i) ≅ openOrdinary q I M i :=
  asIso (ordinaryColimitToOpen q M hM hMb I i)

/-- The constructed colimit comparison agrees with its actual geometric
restriction map on every ideal-power stage. -/
theorem ordinaryColimitToOpen_ι (I : X.IdealSheafData) (i : ℤ) (n : ℕ+) :
    colimit.ι (ordinaryDiagram q M hM hMb I i) n ≫
        ordinaryColimitToOpen q M hM hMb I i =
      ordinaryStageToOpen q M hM hMb I i n := sorry

/-- The constructed colimit identification intertwines the actual ideal
inclusions with the independently constructed geometric ordinary restriction. -/
theorem ordinaryColimitToOpen_naturality {I I' : X.IdealSheafData} (h : I' ≤ I) (i : ℤ) :
    colimMap (ordinaryRestriction q M hM hMb h i) ≫ ordinaryColimitToOpen q M hM hMb I' i =
      ordinaryColimitToOpen q M hM hMb I i ≫ openRestrictionFromIdeals q h M i := sorry

/-- The tower pairing now lands in the dual of geometric ordinary cohomology
on the open complement, using the specified colimit map rather than a free iso. -/
def limitToGeometricOrdinaryDual (I : X.IdealSheafData) (i : ℤ) :
    (limit (compactDiagram q M I i) : ModuleCat.{u} k) →ₗ[k]
      Module.Dual k (openOrdinary q I M i) :=
  (ordinaryColimitIso q M hM hMb I i).inv.hom.dualMap.comp
    (limitPairing q M hM hMb I i)

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.IdealDuality
