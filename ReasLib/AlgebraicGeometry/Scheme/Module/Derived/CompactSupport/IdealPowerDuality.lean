module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Cohomology.DualityStage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Restriction
public import ReasLib.Algebra.Category.ModuleCat.FiniteDual

/-!
# Common ideal-power diagrams for compact-support duality

The ideal stages and inclusions are the existing localized ideal-power complexes.
Ordinary stages use RHom precomposition; compact stages use tensoring by the
same ideal stages. Their pairings are the specified normalized proper pairings.
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

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsNoetherian X]
variable [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]

/-- The fixed cochain representative O_X[0] used by the existing ideal-power
construction, before forming either of the duality diagrams. -/
abbrev unitComplex : CochainComplex X.Modules ℤ :=
  (CochainComplex.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)

/-- Each localized ideal-power stage of O_X is quasicoherent. -/
theorem idealStage_mem (I : X.IdealSheafData) (n : OrderDual ℕ+) :
    ModuleDerived.quasicoherentProperty X ((positiveDerivedSystem I unitComplex).obj n) := sorry

/-- The actual degree-zero derived ideal-power stage, lifted without changing
its data to the quasicoherent full subcategory. -/
def idealStage (I : X.IdealSheafData) (n : OrderDual ℕ+) : Scheme.DerivedQCoh X :=
  ⟨(positiveDerivedSystem I unitComplex).obj n, idealStage_mem I n⟩

/-- The ideal-power stages have coherent cohomology on a Noetherian scheme. -/
theorem idealStage_coherent (I : X.IdealSheafData) (n : OrderDual ℕ+) :
    DerivedCategory.cohomologyIn (SheafOfModules.isCoherent X.ringCatSheaf)
      (idealStage I n).obj := sorry

/-- The ideal-power stages are bounded above, being concentrated in degree zero. -/
theorem idealStage_boundedAbove (I : X.IdealSheafData) (n : OrderDual ℕ+) :
    (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))
      (idealStage I n).obj := sorry

/-- The actual transition between quasicoherent ideal stages is the localized
ideal-power inclusion, with no selected inter-stage map. -/
def idealTransition (I : X.IdealSheafData) {m n : OrderDual ℕ+} (f : m ⟶ n) :
    idealStage I m ⟶ idealStage I n :=
  ObjectProperty.homMk ((positiveDerivedSystem I unitComplex).map f)

/-- Inclusion of ideals gives the existing canonical inclusion at each stage. -/
def idealInclusion {I I' : X.IdealSheafData} (h : I' ≤ I) (n : OrderDual ℕ+) :
    idealStage I' n ⟶ idealStage I n :=
  ObjectProperty.homMk ((idealPowerSystemInclusion h unitComplex).app n)

variable (q : X ⟶ Spec (CommRingCat.of k)) [IsProper q]
variable (M : Scheme.DerivedQCoh X)
variable (hM : DerivedCategory.cohomologyIn (SheafOfModules.isCoherent X.ringCatSheaf) M.obj)
variable (hMb : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) M.obj)

/-- The ordinary direct system H^i(X,RHom(I^n,M)), using the actual derived
ideal stages and their contravariant RHom transitions. -/
def ordinaryDiagram (I : X.IdealSheafData) (i : ℤ) : ℕ+ ⥤ ModuleCat.{u} k where
  obj n := cohomologyOverField q
    (ordinaryStage (idealStage I n) M (idealStage_coherent I n)
      (idealStage_boundedAbove I n) hM hMb) i
  map {m n} f :=
    ordinaryStageCohomologyMap (idealTransition I (homOfLE f.le)) M
      (idealStage_coherent I m) (idealStage_boundedAbove I m)
      (idealStage_coherent I n) (idealStage_boundedAbove I n) hM hMb q i
  map_id := sorry
  map_comp := sorry

/-- The compact inverse system H^{-i}(X,RHom(M,q!O) tensor I^n), with actual
tensor transitions. No bounded-derived stage replacement is assumed. -/
def compactDiagram (I : X.IdealSheafData) (i : ℤ) :
    PNatInverseSystem (ModuleCat.{u} k) where
  obj n := (globalCohomologyOverField q (-i)).obj
    (((ihom M.obj).obj (Scheme.DerivedQCoh.properDualizingComplex q).obj) ⊗ (idealStage I n).obj)
  map f := compactTensorStageMap (idealTransition I f) M q (-i)
  map_id := sorry
  map_comp := sorry

/-- The shift-sign conversion identifies degree -(-i) proper cohomology with
degree i through equality of the integer indices alone. -/
def stagePairing (I : X.IdealSheafData) (i : ℤ) (n : OrderDual ℕ+) :
    (compactDiagram q M I i).obj n →ₗ[k]
      Module.Dual k ((ordinaryDiagram q M hM hMb I i).obj n) :=
  let L := ordinaryStage (idealStage I n) M (idealStage_coherent I n)
    (idealStage_boundedAbove I n) hM hMb
  (eqToIso (congrArg (cohomologyOverField q L) (Int.neg_neg i))).inv.hom.dualMap.comp
    (properTensorStagePairing q (idealStage I n) M (idealStage_coherent I n)
      (idealStage_boundedAbove I n) hM hMb (-i))

/-- The actual stage pairings form a natural transformation into the finite-dual
inverse diagram. Naturality is a law of these maps, not a package input. -/
def pairingDiagram (I : X.IdealSheafData) (i : ℤ) :
    compactDiagram q M I i ⟶ FiniteDual.diagram (ordinaryDiagram q M hM hMb I i) where
  app n := ModuleCat.ofHom (stagePairing q M hM hMb I i n)
  naturality := sorry

/-- Nested ideals induce the ordinary direct-system restriction by RHom
precomposition of their canonical same-power inclusion. -/
def ordinaryRestriction {I I' : X.IdealSheafData} (h : I' ≤ I) (i : ℤ) :
    ordinaryDiagram q M hM hMb I i ⟶ ordinaryDiagram q M hM hMb I' i where
  app n := ordinaryStageCohomologyMap (idealInclusion h n) M
    (idealStage_coherent I n) (idealStage_boundedAbove I n)
    (idealStage_coherent I' n) (idealStage_boundedAbove I' n) hM hMb q i
  naturality := sorry

/-- Nested ideals induce compact restriction by tensoring the same canonical
same-power inclusion. -/
def compactRestriction {I I' : X.IdealSheafData} (h : I' ≤ I) (i : ℤ) :
    compactDiagram q M I' i ⟶ compactDiagram q M I i where
  app n := compactTensorStageMap (idealInclusion h n) M q (-i)
  naturality := sorry

/-- The specified diagram maps commute with the actual normalized pairings. -/
theorem pairingDiagram_restriction {I I' : X.IdealSheafData} (h : I' ≤ I) (i : ℤ) :
    compactRestriction q M h i ≫ pairingDiagram q M hM hMb I i =
      pairingDiagram q M hM hMb I' i ≫
        FiniteDual.diagramMap (ordinaryRestriction q M hM hMb h i) := sorry

/-- The limit pairing is the limit of the actual stage maps followed by the
canonical finite-dual comparison with the ordinary colimit. -/
def limitPairingMap {k : Type u} [Field k]
    (F : PNatInverseSystem (ModuleCat.{u} k)) (G : ℕ+ ⥤ ModuleCat.{u} k)
    (a : F ⟶ FiniteDual.diagram G) :
    (limit F : ModuleCat.{u} k) →ₗ[k] Module.Dual k (colimit G : ModuleCat.{u} k) :=
  (FiniteDual.limitToDualColimit G).comp (limMap a).hom

/-- The concrete ideal-power limit comparison uses the actual pairing diagram. -/
def limitPairing (I : X.IdealSheafData) (i : ℤ) :
    (limit (compactDiagram q M I i) : ModuleCat.{u} k) →ₗ[k]
      Module.Dual k (colimit (ordinaryDiagram q M hM hMb I i) : ModuleCat.{u} k) :=
  limitPairingMap (compactDiagram q M I i) (ordinaryDiagram q M hM hMb I i)
    (pairingDiagram q M hM hMb I i)

/-- The common ideal-power limit/colimit square commutes for the constructed
restriction maps. No chosen comparison iso or compatibility input is needed. -/
theorem limitPairing_restriction {I I' : X.IdealSheafData} (h : I' ≤ I) (i : ℤ) :
    (limitPairing q M hM hMb I i).comp (limMap (compactRestriction q M h i)).hom =
      (colimMap (ordinaryRestriction q M hM hMb h i)).hom.dualMap.comp
        (limitPairing q M hM hMb I' i) := sorry

/-- The specified stage map is bijective by proper duality and the
tensor–RHom comparison for coherent bounded-above ideal stages. -/
theorem stagePairing_bijective (I : X.IdealSheafData) (i : ℤ) (n : OrderDual ℕ+) :
    Function.Bijective (stagePairing q M hM hMb I i n) := sorry

/-- The limit of the specified stage isomorphisms followed by finite duality
is bijective; no independent limit identification is selected. -/
theorem limitPairing_bijective (I : X.IdealSheafData) (i : ℤ) :
    Function.Bijective (limitPairing q M hM hMb I i) := sorry

/-- The source-direction horizontal arrow on the actual common ideal-power
model is the inverse of its specified limit pairing. -/
def dualityEquiv (I : X.IdealSheafData) (i : ℤ) :
    Module.Dual k (colimit (ordinaryDiagram q M hM hMb I i) : ModuleCat.{u} k) ≃ₗ[k]
      (limit (compactDiagram q M I i) : ModuleCat.{u} k) :=
  (LinearEquiv.ofBijective (limitPairing q M hM hMb I i)
    (limitPairing_bijective q M hM hMb I i)).symm

/-- The source-direction square for the actual common ideal-power model.
Its geometric identifications must be supplied by constructed maps before
this theorem is used as the source-facing Lemma 48.33.2. -/
theorem dualityEquiv_restriction {I I' : X.IdealSheafData} (h : I' ≤ I) (i : ℤ) :
    (limMap (compactRestriction q M h i)).hom.comp
        (dualityEquiv q M hM hMb I' i).toLinearMap =
      (dualityEquiv q M hM hMb I i).toLinearMap.comp
        (colimMap (ordinaryRestriction q M hM hMb h i)).hom.dualMap := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.IdealDuality
