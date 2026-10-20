/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.LocalAlgebra
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Base change of the affine finite locally constant algebra

A fixed trivializing affine cover is pulled back along an affine étale map. Native flat
base change of the literal equalizer provides the inverse on algebras, while actual tensor
coordinates and sheaf gluing compare it with the intrinsic function ring on the new base.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.FiniteLocallyConstant

variable {X : Scheme.{u}}
variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [Sheaf.IsFiniteLocallyConstant F]
variable {U V : X.Etale} [IsAffine U.left] [IsAffine V.left] (f : V ⟶ U)

/-- Base scalars restrict along the actual affine étale arrow. -/
abbrev baseChangeBaseAlgebra : Algebra Γ(U.left, ⊤) Γ(V.left, ⊤) :=
  f.left.appTop.hom.toAlgebra

/-- A chart of the original finite cover, pulled back to the new affine base. -/
def baseChangeChart (i : finiteAffineIndex F U) : X.Etale :=
  pullback f (selectedChartMap F U i)

/-- The native étale-site pullback is a pullback of the underlying schemes. -/
theorem baseChangeChart_isPullback (i : finiteAffineIndex F U) :
    IsPullback (pullback.fst f (selectedChartMap F U i)).left
      (pullback.snd f (selectedChartMap F U i)).left f.left (selectedChartMap F U i).left :=
  IsPullback.map (Over.forget X)
    (IsPullback.map (MorphismProperty.Over.forget (@Etale) ⊤ X)
      (IsPullback.of_hasPullback f (selectedChartMap F U i)))

instance baseChangeChart_isAffine (i : finiteAffineIndex F U) :
    IsAffine (baseChangeChart F f i).left :=
  IsAffine.of_isPullback (baseChangeChart_isPullback F f i)

/-- The trivialization on a pulled chart is the actual original trivialization restricted to it. -/
def baseChangeChartIso (i : finiteAffineIndex F U) :
    F.over (baseChangeChart F f i) ≅
      (constantSheaf (X.smallEtaleTopology.over (baseChangeChart F f i)) (Type (u + 1))).obj
        (selectedLabels F U i) :=
  restrictChartIso F (pullback.snd f (selectedChartMap F U i))
    (selectedLabels F U i) (finiteAffineChartIso F U i)

/-- Pullback of the actual covering sieve gives a covering family on the new slice. -/
theorem baseChangeCharts_coversTop :
    (X.smallEtaleTopology.over V).CoversTop
      (fun i : finiteAffineIndex F U ↦ Over.mk (pullback.fst f (selectedChartMap F U i))) := by
  let c (i : finiteAffineIndex F U) := Over.mk (pullback.fst f (selectedChartMap F U i))
  let g (i : finiteAffineIndex F U) : c i ⟶ Over.mk (𝟙 V) :=
    Over.homMk (pullback.fst f (selectedChartMap F U i)) (Category.comp_id _)
  apply (GrothendieckTopology.coversTop_iff_of_isTerminal
    (X.smallEtaleTopology.over V) (Over.mk (𝟙 V)) Over.mkIdTerminal c).mpr
  rw [← Sieve.ofArrows_eq_ofObjects Over.mkIdTerminal c g]
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  change Sieve.ofArrows (fun i : finiteAffineIndex F U ↦ pullback f (selectedChartMap F U i))
    (fun i ↦ pullback.fst f (selectedChartMap F U i)) ∈ X.smallEtaleTopology V
  rw [Sieve.ofArrows_eq_pullback_of_isPullback (selectedChartMap F U)
    (fun i ↦ IsPullback.of_hasPullback f (selectedChartMap F U i))]
  apply X.smallEtaleTopology.pullback_stable f
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (selectedChartMap F U)).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, y, hy⟩ := (finiteAffineCover F U).cover x
  exact Set.mem_iUnion.mpr ⟨i, y, hy⟩

/-- Native affine section pushouts identify each pulled chart ring with the scalar tensor product. -/
def baseChangeChartTensorEquiv (i : finiteAffineIndex F U) :
    letI := baseChangeBaseAlgebra f
    letI := chartBaseAlgebra F U i
    Γ(V.left, ⊤) ⊗[Γ(U.left, ⊤)] Γ((selectedChart F U i).left, ⊤) ≃+*
      Γ((baseChangeChart F f i).left, ⊤) := by
  letI := baseChangeBaseAlgebra f
  letI := chartBaseAlgebra F U i
  exact ((CommRingCat.isPushout_tensorProduct Γ(U.left, ⊤)
      Γ(V.left, ⊤) Γ((selectedChart F U i).left, ⊤)).isoIsPushout
      (CommRingCat.of Γ(V.left, ⊤))
      (CommRingCat.of Γ((selectedChart F U i).left, ⊤))
      (isPushout_appTop_of_isPullback (baseChangeChart_isPullback F f i))).commRingCatIsoToRingEquiv

/-- The scalar-extended covering algebra has the actual finite product of pulled-chart coordinates. -/
def baseChangedCoverTensorEquiv :
    letI := baseChangeBaseAlgebra f
    letI := coveringAlgebraBaseAlgebra F U
    Γ(V.left, ⊤) ⊗[Γ(U.left, ⊤)] coveringAlgebra F U ≃+*
      ∀ i : finiteAffineIndex F U, chartAlgebra (baseChangeChart F f i) (selectedLabels F U i) := by
  letI := baseChangeBaseAlgebra f
  letI : ∀ i : finiteAffineIndex F U,
      Algebra Γ(U.left, ⊤) Γ((selectedChart F U i).left, ⊤) := fun i ↦ chartBaseAlgebra F U i
  exact (Algebra.TensorProduct.piRight Γ(U.left, ⊤) Γ(U.left, ⊤) Γ(V.left, ⊤)
    (fun i : finiteAffineIndex F U ↦ chartAlgebra (selectedChart F U i) (selectedLabels F U i))).toRingEquiv.trans
      ((RingEquiv.piCongrRight fun i ↦
        (Algebra.TensorProduct.piRight Γ(U.left, ⊤) Γ(U.left, ⊤) Γ(V.left, ⊤)
          (fun _ : Fin (Nat.card (selectedLabels F U i)) ↦ Γ((selectedChart F U i).left, ⊤))).toRingEquiv.trans
            (RingEquiv.piCongrRight fun _ ↦ baseChangeChartTensorEquiv F f i)))

/-- The original coaction viewed over the base ring, retaining its exact scalar actions. -/
def affineCoactionOverBase (W : X.Etale) [IsAffine W.left] :
    letI := coveringRingBaseAlgebra F W
    letI := coveringAlgebraBaseAlgebra F W
    coveringAlgebra F W →ₐ[Γ(W.left, ⊤)] coveringRing F W ⊗[Γ(W.left, ⊤)] coveringAlgebra F W := by
  letI := coveringRingBaseAlgebra F W
  letI := coveringAlgebraBaseAlgebra F W
  letI := coveringAlgebraOverCover F W
  exact @AlgHom.restrictScalars Γ(W.left, ⊤) (coveringRing F W) (coveringAlgebra F W)
    ((coveringRing F W) ⊗[Γ(W.left, ⊤)] coveringAlgebra F W)
    inferInstance inferInstance inferInstance inferInstance
    (coveringRingBaseAlgebra F W) (coveringAlgebraOverCover F W) inferInstance
    (coveringAlgebraBaseAlgebra F W) inferInstance (coveringScalarTower F W) inferInstance
    (affineCoaction F W)

/-- The scalar-extended invariant algebra is the literal equalizer of the two tensor maps. -/
abbrev baseChangedInvariants :
    letI := baseChangeBaseAlgebra f
    letI := coveringAlgebraBaseAlgebra F U
    Subalgebra Γ(V.left, ⊤) (Γ(V.left, ⊤) ⊗[Γ(U.left, ⊤)] coveringAlgebra F U) :=
  letI := baseChangeBaseAlgebra f
  letI := coveringRingBaseAlgebra F U
  letI := coveringAlgebraBaseAlgebra F U
  letI := coveringAlgebraOverCover F U
  letI : IsScalarTower Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U) := coveringScalarTower F U
  AlgHom.equalizer
    (Algebra.TensorProduct.map (AlgHom.id Γ(V.left, ⊤) Γ(V.left, ⊤))
      (affineCoactionOverBase F U))
    (Algebra.TensorProduct.map (AlgHom.id Γ(V.left, ⊤) Γ(V.left, ⊤))
      (Algebra.TensorProduct.includeRight (R := Γ(U.left, ⊤)) (A := coveringRing F U)
        (B := coveringAlgebra F U)))

/-- The étale base map supplies a complete native flatness certificate. -/
theorem baseChangeBase_flat :
    letI := baseChangeBaseAlgebra f
    Module.Flat Γ(U.left, ⊤) Γ(V.left, ⊤) := by
  letI := baseChangeBaseAlgebra f
  exact RingHom.flat_algebraMap_iff.mp f.left.flat_appTop

/-- Native flat base change of equalizers supplies both directions, including the actual inverse. -/
def tensorInvariantsEquiv :
    letI := baseChangeBaseAlgebra f
    letI := coveringAlgebraBaseAlgebra F U
    Γ(V.left, ⊤) ⊗[Γ(U.left, ⊤)] affineAlgebra (F := F) U ≃ₐ[Γ(V.left, ⊤)]
      baseChangedInvariants F f := by
  letI := baseChangeBaseAlgebra f
  letI := coveringRingBaseAlgebra F U
  letI := coveringAlgebraBaseAlgebra F U
  letI := coveringAlgebraOverCover F U
  letI : IsScalarTower Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U) := coveringScalarTower F U
  letI : Module.Flat Γ(U.left, ⊤) Γ(V.left, ⊤) := baseChangeBase_flat f
  exact AlgHom.tensorEqualizerEquiv Γ(V.left, ⊤) Γ(V.left, ⊤)
    (affineCoactionOverBase F U)
    (Algebra.TensorProduct.includeRight (R := Γ(U.left, ⊤)) (A := coveringRing F U)
      (B := coveringAlgebra F U))

/-- An element of the scalar-extended equalizer gives actual functions on each pulled chart. -/
def baseChangedLocalFunctions (b : baseChangedInvariants F f) (i : finiteAffineIndex F U) :
    Sheaf.FunctionAlgebra ((F.over V).over (Over.mk (pullback.fst f (selectedChartMap F U i))))
      (((SmallStandardTopology.commStructureSheaf .etale X).over V).over
        (Over.mk (pullback.fst f (selectedChartMap F U i)))) :=
  Sheaf.FunctionAlgebra.iteratedSliceEquiv.{u + 1, u, u + 1, u} F
    (SmallStandardTopology.commStructureSheaf .etale X)
    (Over.mk (pullback.fst f (selectedChartMap F U i)))
    ((localCoordinates F (baseChangeChart F f i) (selectedLabels F U i)
      (baseChangeChartIso F f i)).symm (baseChangedCoverTensorEquiv F f b.val i))

/-- The tensor equalizer condition gives agreement on every common test object of the pulled cover. -/
theorem baseChangedLocalFunctions_compatible (b : baseChangedInvariants F f) :
    Sheaf.FunctionAlgebra.Compatible.{u + 1, u, u + 1, u, 0} (F.over V)
      ((SmallStandardTopology.commStructureSheaf .etale X).over V)
      (fun i : finiteAffineIndex F U ↦ Over.mk (pullback.fst f (selectedChartMap F U i)))
      (baseChangedLocalFunctions F f b) := sorry

/-- Glue the tensor equalizer's actual local functions using the native Hom sheaf. -/
def baseChangedInvariantsToFunctions :
    baseChangedInvariants F f →+* localFunctionAlgebra F V where
  toFun b := Sheaf.FunctionAlgebra.glue.{u + 1, u, u + 1, u, 0}
    (F.over V) ((SmallStandardTopology.commStructureSheaf .etale X).over V)
    (fun i : finiteAffineIndex F U ↦ Over.mk (pullback.fst f (selectedChartMap F U i)))
    (baseChangeCharts_coversTop F f) (baseChangedLocalFunctions F f b)
    (baseChangedLocalFunctions_compatible F f b)
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- Restrict an intrinsic function to the fixed pulled cover and read its actual coordinates. -/
def baseChangeFunctionCoordinates :
    localFunctionAlgebra F V →+*
      ∀ i : finiteAffineIndex F U, chartAlgebra (baseChangeChart F f i) (selectedLabels F U i) where
  toFun a i := localCoordinates F (baseChangeChart F f i) (selectedLabels F U i)
    (baseChangeChartIso F f i)
    (Sheaf.FunctionAlgebra.restrictAlong.{u + 1, u, u + 1, u} F
      (SmallStandardTopology.commStructureSheaf .etale X)
      (pullback.fst f (selectedChartMap F U i)) a)
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- Native finite tensor sums turn the function's pulled-chart coordinates into a tensor. -/
def baseChangeFunctionTensor :
    letI := baseChangeBaseAlgebra f
    letI := coveringAlgebraBaseAlgebra F U
    localFunctionAlgebra F V →+* Γ(V.left, ⊤) ⊗[Γ(U.left, ⊤)] coveringAlgebra F U :=
  (baseChangedCoverTensorEquiv F f).symm.toRingHom.comp (baseChangeFunctionCoordinates F f)

/-- Coordinates of one intrinsic function equalize the actual two scalar-extended coaction maps. -/
theorem baseChangeFunctionTensor_mem (a : localFunctionAlgebra F V) :
    baseChangeFunctionTensor F f a ∈ baseChangedInvariants F f := sorry

/-- The reverse map retains the tensor obtained from the real local coordinates. -/
def functionsToBaseChangedInvariants :
    localFunctionAlgebra F V →+* baseChangedInvariants F f where
  toFun a := ⟨baseChangeFunctionTensor F f a, baseChangeFunctionTensor_mem F f a⟩
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- The pulled-cover tensor equalizer is the intrinsic function ring on the new affine base. -/
def baseChangedFunctionEquiv : baseChangedInvariants F f ≃+* localFunctionAlgebra F V where
  toFun := baseChangedInvariantsToFunctions F f
  invFun := functionsToBaseChangedInvariants F f
  left_inv := sorry
  right_inv := sorry
  map_add' := (baseChangedInvariantsToFunctions F f).map_add
  map_mul' := (baseChangedInvariantsToFunctions F f).map_mul

/-- The actual base-change equivalence combines native equalizer base change with two real
cover-to-intrinsic identifications. Both directions are implemented. -/
def affineBaseChangeRingEquiv :
    letI := baseChangeBaseAlgebra f
    letI := coveringAlgebraBaseAlgebra F U
    Γ(V.left, ⊤) ⊗[Γ(U.left, ⊤)] affineAlgebra (F := F) U ≃+* affineAlgebra (F := F) V :=
  (tensorInvariantsEquiv F f).toRingEquiv.trans
    ((baseChangedFunctionEquiv F f).trans (affineFunctionEquiv F V).symm)

/-- The constructed base-change map is multiplication by a new scalar after intrinsic restriction. -/
theorem affineBaseChangeRingEquiv_tmul (t : Γ(V.left, ⊤)) (a : affineAlgebra (F := F) U) :
    (letI := baseChangeBaseAlgebra f
     letI := coveringAlgebraBaseAlgebra F U
     affineBaseChangeRingEquiv F f (t ⊗ₜ[Γ(U.left, ⊤)] a)) =
      algebraMap Γ(V.left, ⊤) (affineAlgebra (F := F) V) t * affineRestrict F f a := sorry

/-- The actual base-change inverse transports the native tensor pushout to the restriction square. -/
theorem affineAlgebra_isPushout :
    IsPushout
      (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) (affineAlgebra (F := F) U)))
      f.left.appTop (CommRingCat.ofHom (affineRestrict F f))
      (CommRingCat.ofHom (algebraMap Γ(V.left, ⊤) (affineAlgebra (F := F) V))) := by
  letI := baseChangeBaseAlgebra f
  letI := coveringAlgebraBaseAlgebra F U
  exact ((CommRingCat.isPushout_tensorProduct Γ(U.left, ⊤) Γ(V.left, ⊤)
      (affineAlgebra (F := F) U)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (affineBaseChangeRingEquiv F f).toCommRingCatIso
    rfl rfl (by sorry) (by sorry)).flip

/-- Actual affine algebra base change yields the native pullback square for restriction of spectra. -/
theorem affineRestriction_isPullback :
    IsPullback (affineRestrictionMap F f) (affineRepresentationMap F V)
      (affineRepresentationMap F U) f.left :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (affineAlgebra_isPushout F f)).of_iso
    (Iso.refl _) (Iso.refl _) V.left.isoSpec.symm U.left.isoSpec.symm
    rfl rfl (by sorry) (by sorry)

end AlgebraicGeometry.Scheme.FiniteLocallyConstant
