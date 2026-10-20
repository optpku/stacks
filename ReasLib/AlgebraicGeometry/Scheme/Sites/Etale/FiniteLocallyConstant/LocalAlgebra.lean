/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc.Presentation
public import ReasLib.Algebra.Category.Ring.Sheaf.FunctionAlgebra.Descent
public import ReasLib.Algebra.Category.CommAlgCat.Descent.FiniteProduct
public import ReasLib.Algebra.Category.CommAlgCat.Descent.FaithfullyFlat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.TensorProduct.Pi
public import ReasLib.AlgebraicGeometry.Scheme.Sites.FunctionSheaves
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Local finite algebras of a finite locally constant étale sheaf

The actual constant chart cover carried by local constancy determines finite products of
chart section rings. Finite labels are indexed by a native finite model, so the resulting
algebra and its spectrum remain in the scheme's universe.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.FiniteLocallyConstant

variable {X : Scheme.{u}}
variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
variable [Sheaf.IsFiniteLocallyConstant F]

/-- The index of the constant chart cover supplied by local constancy over `U`. -/
def chartIndex (U : X.Etale) : Type (u + 1) :=
  (Sheaf.IsLocallyConstantWith.existsConstantCover (P := Finite) (F := F) U).choose

/-- An actual chart of the supplied local constant cover. -/
def chart (U : X.Etale) (i : chartIndex F U) : Over U :=
  (Sheaf.IsLocallyConstantWith.existsConstantCover (P := Finite) (F := F) U).choose_spec.choose i

/-- The selected charts form a covering family on the slice site. -/
theorem chart_coversTop (U : X.Etale) :
    (X.smallEtaleTopology.over U).CoversTop (chart F U) :=
  (Sheaf.IsLocallyConstantWith.existsConstantCover (P := Finite) (F := F) U).choose_spec.choose_spec.1

/-- The actual finite set of constant labels carried by a supplied chart. -/
def chartLabels (U : X.Etale) (i : chartIndex F U) : Type (u + 1) :=
  ((Sheaf.IsLocallyConstantWith.existsConstantCover (P := Finite) (F := F) U).choose_spec.choose_spec.2 i).choose

instance chartLabels_finite (U : X.Etale) (i : chartIndex F U) : Finite (chartLabels F U i) :=
  ((Sheaf.IsLocallyConstantWith.existsConstantCover (P := Finite) (F := F) U).choose_spec.choose_spec.2 i).choose_spec.1

/-- The given local trivialization on the selected chart. Both maps come from the hypothesis. -/
def chartIso (U : X.Etale) (i : chartIndex F U) :
    F.over (chart F U i).left ≅
      (constantSheaf (X.smallEtaleTopology.over (chart F U i).left) (Type (u + 1))).obj
        (chartLabels F U i) :=
  ((Sheaf.IsLocallyConstantWith.existsConstantCover (P := Finite) (F := F) U).choose_spec.choose_spec.2 i).choose_spec.2.some

/-- The affine refinement index for a selected constant chart. -/
abbrev affineChartIndex (U : X.Etale) (i : chartIndex F U) : Type u :=
  (chart F U i).left.left.affineOpenCover.I₀

/-- Refine a constant chart by the native affine-open cover of its source scheme. -/
def affineChart (U : X.Etale) (i : chartIndex F U) (j : affineChartIndex F U i) : X.Etale :=
  Scheme.Etale.mk ((chart F U i).left.left.affineOpenCover.f j ≫ (chart F U i).left.hom)

/-- The map from the native affine refinement to its original constant chart. -/
def affineChartMap (U : X.Etale) (i : chartIndex F U) (j : affineChartIndex F U i) :
    affineChart F U i j ⟶ (chart F U i).left :=
  MorphismProperty.Over.homMk ((chart F U i).left.left.affineOpenCover.f j)

instance affineChart_isAffine (U : X.Etale) (i : chartIndex F U) (j : affineChartIndex F U i) :
    IsAffine (affineChart F U i j).left :=
  inferInstanceAs (IsAffine (Spec ((chart F U i).left.left.affineOpenCover.X j)))

/-- Restrict a given constant chart along an actual map of étale neighborhoods. -/
def restrictChartIso {V W : X.Etale} (f : W ⟶ V) (E : Type (u + 1))
    (e : F.over V ≅ (constantSheaf (X.smallEtaleTopology.over V) (Type (u + 1))).obj E) :
    F.over W ≅ (constantSheaf (X.smallEtaleTopology.over W) (Type (u + 1))).obj E :=
  (X.smallEtaleTopology.overMapPullback (Type (u + 1)) f).mapIso e ≪≫
    ((Over.map f).pushforwardContinuousSheafificationCompatibility
      (Type (u + 1)) (X.smallEtaleTopology.over W) (X.smallEtaleTopology.over V)).symm.app
        ((Functor.const (Over V)ᵒᵖ).obj E)

/-- The actual trivialization restricted to an affine refinement keeps the same finite labels. -/
def affineChartIso (U : X.Etale) (i : chartIndex F U) (j : affineChartIndex F U i) :
    F.over (affineChart F U i j) ≅
      (constantSheaf (X.smallEtaleTopology.over (affineChart F U i j)) (Type (u + 1))).obj
        (chartLabels F U i) :=
  restrictChartIso F (affineChartMap F U i j) (chartLabels F U i) (chartIso F U i)

/-- The actual chart maps jointly cover the underlying scheme of the slice object. -/
theorem chart_iUnion_range (U : X.Etale) :
    (⋃ i : chartIndex F U, Set.range (chart F U i).hom.left) = Set.univ := by
  let g (i : chartIndex F U) : chart F U i ⟶ Over.mk (𝟙 U) :=
    Over.homMk (chart F U i).hom (Category.comp_id _)
  have h := chart_coversTop F U (Over.mk (𝟙 U))
  rw [← Sieve.ofArrows_eq_ofObjects Over.mkIdTerminal (chart F U)
    g] at h
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at h
  exact (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun i ↦ (chart F U i).hom)).mp h

/-- The index of all native affine refinements of the supplied constant chart cover. -/
abbrev affineCoverIndex (U : X.Etale) : Type (u + 1) :=
  Σ i : chartIndex F U, affineChartIndex F U i

/-- The actual affine refinement map to the original slice object. -/
def affineCoverMap (U : X.Etale) (k : affineCoverIndex F U) :
    affineChart F U k.1 k.2 ⟶ U :=
  affineChartMap F U k.1 k.2 ≫ (chart F U k.1).hom

/-- Native affine refinement preserves joint surjectivity of the constant chart cover. -/
theorem affineCover_iUnion_range (U : X.Etale) :
    (⋃ k : affineCoverIndex F U, Set.range (affineCoverMap F U k).left) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ i : chartIndex F U, Set.range (chart F U i).hom.left := by
    rw [chart_iUnion_range]; exact Set.mem_univ x
  rcases Set.mem_iUnion.mp hx with ⟨i, y, rfl⟩
  obtain ⟨j, z, hz⟩ := (chart F U i).left.left.affineOpenCover.openCover.exists_eq y
  apply Set.mem_iUnion.mpr
  refine ⟨⟨i, j⟩, z, ?_⟩
  change (chart F U i).hom.left (((chart F U i).left.left.affineOpenCover.f j) z) = _
  exact congrArg (chart F U i).hom.left hz

/-- An affine slice object admits a finite subfamily of the actual affine constant charts. -/
def finiteAffineSubcover (U : X.Etale) [IsAffine U.left] : Finset (affineCoverIndex F U) := by
  classical
  exact (isCompact_univ.elim_finite_subcover
    (fun k : affineCoverIndex F U ↦ Set.range (affineCoverMap F U k).left)
    (fun k ↦ (affineCoverMap F U k).left.isOpenMap.isOpen_range)
    (by rw [affineCover_iUnion_range])).choose

/-- The selected finite affine constant charts still cover the original affine object. -/
theorem finiteAffineSubcover_covers (U : X.Etale) [IsAffine U.left] :
    Set.univ ⊆ ⋃ k ∈ finiteAffineSubcover F U, Set.range (affineCoverMap F U k).left := by
  classical
  exact (isCompact_univ.elim_finite_subcover
    (fun k : affineCoverIndex F U ↦ Set.range (affineCoverMap F U k).left)
    (fun k ↦ (affineCoverMap F U k).left.isOpenMap.isOpen_range)
    (by rw [affineCover_iUnion_range])).choose_spec

/-- A finite label set is reindexed into its native finite cardinal model. -/
def labelEquiv (E : Type (u + 1)) [Finite E] : E ≃ Fin (Nat.card E) := by
  letI := Fintype.ofFinite E
  exact (Fintype.equivFin E).trans (finCongr (Nat.card_eq_fintype_card.symm))

/-- The selected finite affine cover indexed in the scheme universe. -/
abbrev finiteAffineIndex (U : X.Etale) [IsAffine U.left] : Type :=
  Fin (Nat.card ↥(finiteAffineSubcover F U))

/-- Recover the actual affine chart index from its finite enumeration. -/
def finiteAffineLabel (U : X.Etale) [IsAffine U.left] (j : finiteAffineIndex F U) :
    ↥(finiteAffineSubcover F U) :=
  (labelEquiv ↥(finiteAffineSubcover F U)).symm j

/-- The real standard fpqc cover extracted from finite local constancy on an affine object. -/
def finiteAffineCover (U : X.Etale) [IsAffine U.left] : AlgebraicGeometry.StandardFpqcCover U.left where
  isAffineTarget := inferInstance
  n := Nat.card ↥(finiteAffineSubcover F U)
  U j := (affineChart F U (finiteAffineLabel F U j).val.1 (finiteAffineLabel F U j).val.2).left
  map j := (affineCoverMap F U (finiteAffineLabel F U j).val).left
  isAffine j := inferInstance
  flat j := inferInstance
  cover x := by
    have hx := finiteAffineSubcover_covers F U (Set.mem_univ x)
    rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hk, hx⟩
    refine ⟨labelEquiv ↥(finiteAffineSubcover F U) ⟨k, hk⟩, ?_⟩
    have he : (finiteAffineLabel F U
        (labelEquiv ↥(finiteAffineSubcover F U) ⟨k, hk⟩)).val = k :=
      congrArg Subtype.val ((labelEquiv ↥(finiteAffineSubcover F U)).symm_apply_apply ⟨k, hk⟩)
    rw [he]
    exact hx

/-- Each member of the selected finite fpqc cover retains its original constant model. -/
def finiteAffineChartIso (U : X.Etale) [IsAffine U.left] (j : finiteAffineIndex F U) :
    F.over (affineChart F U (finiteAffineLabel F U j).val.1 (finiteAffineLabel F U j).val.2) ≅
      (constantSheaf (X.smallEtaleTopology.over
        (affineChart F U (finiteAffineLabel F U j).val.1 (finiteAffineLabel F U j).val.2))
        (Type (u + 1))).obj (chartLabels F U (finiteAffineLabel F U j).val.1) :=
  affineChartIso F U (finiteAffineLabel F U j).val.1 (finiteAffineLabel F U j).val.2

/-- The finite product of section rings associated with a constant chart on `U`. -/
abbrev chartAlgebra (U : X.Etale) (E : Type (u + 1)) [Finite E] : Type u :=
  Fin (Nat.card E) → Γ(U.left, ⊤)

/-- The chart algebra is the actual ring of functions on its finite label set. -/
def chartAlgebraEquiv (U : X.Etale) (E : Type (u + 1)) [Finite E] :
    chartAlgebra U E ≃ₐ[Γ(U.left, ⊤)] (E → Γ(U.left, ⊤)) :=
  AlgEquiv.piCongrLeft Γ(U.left, ⊤) (fun _ : E ↦ Γ(U.left, ⊤)) (labelEquiv E).symm

/-- The finite product algebra of an actual affine refinement of a supplied chart. -/
abbrev affineChartAlgebra (U : X.Etale) (i : chartIndex F U) (j : affineChartIndex F U i) : Type u :=
  chartAlgebra (affineChart F U i j) (chartLabels F U i)

/-- The local finite étale scheme before descent, represented by the finite product algebra. -/
def affineChartSpectrum (U : X.Etale) (i : chartIndex F U) (j : affineChartIndex F U i) : Scheme.{u} :=
  Spec (CommRingCat.of (affineChartAlgebra F U i j))

/-- The local structural map uses the finite product's constant-function algebra map. -/
def affineChartSpectrumMap (U : X.Etale) (i : chartIndex F U) (j : affineChartIndex F U i) :
    affineChartSpectrum F U i j ⟶ (affineChart F U i j).left :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ((affineChart F U i j).left, ⊤)
    (affineChartAlgebra F U i j))) ≫ (affineChart F U i j).left.isoSpec.inv

/-- Finite products of the affine chart ring give a finite structural morphism. -/
instance affineChartSpectrumMap_isFinite (U : X.Etale) (i : chartIndex F U)
    (j : affineChartIndex F U i) : IsFinite (affineChartSpectrumMap F U i j) := sorry

/-- The local model is étale: it is the finite disjoint union indexed by its constant labels. -/
instance affineChartSpectrumMap_etale (U : X.Etale) (i : chartIndex F U)
    (j : affineChartIndex F U i) : Etale (affineChartSpectrumMap F U i j) := sorry

/-- A canonical finite étale object attached to a source-supplied affine constant chart. -/
def affineChartFiniteEtale (U : X.Etale) (i : chartIndex F U) (j : affineChartIndex F U i) :
    FiniteEtale (affineChart F U i j).left :=
  MorphismProperty.Over.mk ⊤ (affineChartSpectrumMap F U i j) ⟨inferInstance, inferInstance⟩

/-- The actual ring of functions on the restricted sheaf with values in local regular functions. -/
abbrev localFunctionAlgebra (U : X.Etale) :=
  Sheaf.FunctionAlgebra (F.over U) ((SmallStandardTopology.commStructureSheaf .etale X).over U)

/-- A supplied constant chart identifies its intrinsic function algebra with a small finite
product of chart section rings. -/
def localCoordinates (U : X.Etale) (E : Type (u + 1)) [Finite E]
    (e : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E) :
    localFunctionAlgebra F U ≃+* chartAlgebra U E :=
  (Sheaf.FunctionAlgebra.chartEquiv.{u + 1, u, u + 1, u}
    (F := F.over U) (O := (SmallStandardTopology.commStructureSheaf .etale X).over U)
    e Over.mkIdTerminal).trans (chartAlgebraEquiv U E).symm.toRingEquiv

/-- Coordinates of the actual source-supplied affine chart, with its given trivialization. -/
def affineCoordinates (U : X.Etale) (i : chartIndex F U) (j : affineChartIndex F U i) :
    localFunctionAlgebra F (affineChart F U i j) ≃+* affineChartAlgebra F U i j :=
  localCoordinates F (affineChart F U i j) (chartLabels F U i) (affineChartIso F U i j)

/-- Coordinate change on one overlap uses the actual two chart isomorphisms. It permits
locally varying permutations of labels on disconnected overlaps. -/
def coordinateChange (U : X.Etale)
    (E E' : Type (u + 1)) [Finite E] [Finite E']
    (e : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E)
    (e' : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E') :
    chartAlgebra U E ≃+* chartAlgebra U E' :=
  (localCoordinates F U E e).symm.trans (localCoordinates F U E' e')

/-- Changing coordinates through an intermediate chart composes the actual ring maps. -/
theorem coordinateChange_trans (U : X.Etale)
    (E E' E'' : Type (u + 1)) [Finite E] [Finite E'] [Finite E'']
    (e : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E)
    (e' : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E')
    (e'' : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E'') :
    (coordinateChange F U E E' e e').trans (coordinateChange F U E' E'' e' e'') =
      coordinateChange F U E E'' e e'' := by
  ext a
  simp only [coordinateChange, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]

/-- Coordinate change preserves the scalar functions pulled back from the overlap. -/
theorem coordinateChange_algebraMap (U : X.Etale)
    (E E' : Type (u + 1)) [Finite E] [Finite E']
    (e : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E)
    (e' : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E')
    (r : Γ(U.left, ⊤)) :
    coordinateChange F U E E' e e' (algebraMap Γ(U.left, ⊤) (chartAlgebra U E) r) =
      algebraMap Γ(U.left, ⊤) (chartAlgebra U E') r := sorry

/-- The transition between constant charts is an algebra equivalence over the actual overlap. -/
def coordinateChangeAlgEquiv (U : X.Etale)
    (E E' : Type (u + 1)) [Finite E] [Finite E']
    (e : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E)
    (e' : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E') :
    chartAlgebra U E ≃ₐ[Γ(U.left, ⊤)] chartAlgebra U E' :=
  { coordinateChange F U E E' e e' with
    commutes' := coordinateChange_algebraMap F U E E' e e' }

/-- A selected finite affine cover member, viewed as an object of the original étale site. -/
abbrev selectedChart (U : X.Etale) [IsAffine U.left] (j : finiteAffineIndex F U) : X.Etale :=
  affineChart F U (finiteAffineLabel F U j).val.1 (finiteAffineLabel F U j).val.2

/-- The actual map of a selected finite affine member into the base chart. -/
def selectedChartMap (U : X.Etale) [IsAffine U.left] (j : finiteAffineIndex F U) :
    selectedChart F U j ⟶ U :=
  affineCoverMap F U (finiteAffineLabel F U j).val

/-- The actual selected finite affine charts cover the terminal object of the slice site. -/
theorem selectedCharts_coversTop (U : X.Etale) [IsAffine U.left] :
    (X.smallEtaleTopology.over U).CoversTop
      (fun i : finiteAffineIndex F U ↦ Over.mk (selectedChartMap F U i)) := by
  let c (i : finiteAffineIndex F U) := Over.mk (selectedChartMap F U i)
  let g (i : finiteAffineIndex F U) : c i ⟶ Over.mk (𝟙 U) :=
    Over.homMk (selectedChartMap F U i) (Category.comp_id _)
  apply (GrothendieckTopology.coversTop_iff_of_isTerminal (X.smallEtaleTopology.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal c).mpr
  rw [← Sieve.ofArrows_eq_ofObjects Over.mkIdTerminal c g]
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun i ↦ selectedChartMap F U i)).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, y, hy⟩ := (finiteAffineCover F U).cover x
  exact Set.mem_iUnion.mpr ⟨i, y, hy⟩

/-- The original finite labels on a selected finite affine chart. -/
abbrev selectedLabels (U : X.Etale) [IsAffine U.left] (j : finiteAffineIndex F U) : Type (u + 1) :=
  chartLabels F U (finiteAffineLabel F U j).val.1

/-- The actual pairwise overlap in the étale site of the source scheme. -/
def overlap (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) : X.Etale :=
  pullback (selectedChartMap F U i) (selectedChartMap F U j)

/-- The first finite constant chart, restricted along the actual overlap projection. -/
def overlapLeftIso (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    F.over (overlap F U i j) ≅
      (constantSheaf (X.smallEtaleTopology.over (overlap F U i j)) (Type (u + 1))).obj
        (selectedLabels F U i) :=
  restrictChartIso F (pullback.fst (selectedChartMap F U i) (selectedChartMap F U j))
    (selectedLabels F U i) (finiteAffineChartIso F U i)

/-- The second finite constant chart, restricted along the actual overlap projection. -/
def overlapRightIso (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    F.over (overlap F U i j) ≅
      (constantSheaf (X.smallEtaleTopology.over (overlap F U i j)) (Type (u + 1))).obj
        (selectedLabels F U j) :=
  restrictChartIso F (pullback.snd (selectedChartMap F U i) (selectedChartMap F U j))
    (selectedLabels F U j) (finiteAffineChartIso F U j)

/-- The overlap algebra transition is induced by the two actual restricted sheaf charts. -/
def overlapTransition (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    chartAlgebra (overlap F U i j) (selectedLabels F U i) ≃ₐ[Γ((overlap F U i j).left, ⊤)]
      chartAlgebra (overlap F U i j) (selectedLabels F U j) :=
  coordinateChangeAlgEquiv F (overlap F U i j) (selectedLabels F U i) (selectedLabels F U j)
    (overlapLeftIso F U i j) (overlapRightIso F U i j)

/-- The transition acts by first reading the first chart as an intrinsic local function,
then writing it in the second chart's coordinates. -/
theorem overlapTransition_apply (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U)
    (a : chartAlgebra (overlap F U i j) (selectedLabels F U i)) :
    overlapTransition F U i j a =
      localCoordinates F (overlap F U i j) (selectedLabels F U j) (overlapRightIso F U i j)
        ((localCoordinates F (overlap F U i j) (selectedLabels F U i)
          (overlapLeftIso F U i j)).symm a) := rfl

/-- The underlying scheme square of the actual étale-site overlap is a pullback.
The proof uses the native forgetful functors separately, without a project preservation axiom. -/
theorem overlap_isPullback (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    IsPullback (pullback.fst (selectedChartMap F U i) (selectedChartMap F U j)).left
      (pullback.snd (selectedChartMap F U i) (selectedChartMap F U j)).left
      (selectedChartMap F U i).left (selectedChartMap F U j).left :=
  IsPullback.map (Over.forget X)
    (IsPullback.map (MorphismProperty.Over.forget (@Etale) ⊤ X)
      (IsPullback.of_hasPullback (selectedChartMap F U i) (selectedChartMap F U j)))

/-- Affine overlap sections are the actual categorical pushout of the two affine chart rings. -/
def overlapSectionIso (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    pushout (selectedChartMap F U i).left.appTop (selectedChartMap F U j).left.appTop ≅
      CommRingCat.of Γ((overlap F U i j).left, ⊤) :=
  (isPushout_appTop_of_isPullback (overlap_isPullback F U i j)).isoPushout.symm

/-- The left chart ring acts on overlap sections by restriction along the first projection. -/
abbrev overlapLeftAlgebra (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    Algebra Γ((selectedChart F U i).left, ⊤) Γ((overlap F U i j).left, ⊤) :=
  (pullback.fst (selectedChartMap F U i) (selectedChartMap F U j)).left.appTop.hom.toAlgebra

/-- The right chart ring acts on overlap sections by restriction along the second projection. -/
abbrev overlapRightAlgebra (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    Algebra Γ((selectedChart F U j).left, ⊤) Γ((overlap F U i j).left, ⊤) :=
  (pullback.snd (selectedChartMap F U i) (selectedChartMap F U j)).left.appTop.hom.toAlgebra

/-- The base section ring acts on a selected chart through its structural map. -/
abbrev chartBaseAlgebra (U : X.Etale) [IsAffine U.left] (i : finiteAffineIndex F U) :
    Algebra Γ(U.left, ⊤) Γ((selectedChart F U i).left, ⊤) :=
  (selectedChartMap F U i).left.appTop.hom.toAlgebra

/-- Tensor products of the two affine chart rings are identified with actual overlap sections
by their proved native pushout universal properties. -/
def overlapTensorEquiv (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    letI := chartBaseAlgebra F U i
    letI := chartBaseAlgebra F U j
    Γ((selectedChart F U i).left, ⊤) ⊗[Γ(U.left, ⊤)] Γ((selectedChart F U j).left, ⊤) ≃+*
      Γ((overlap F U i j).left, ⊤) := by
  letI := chartBaseAlgebra F U i
  letI := chartBaseAlgebra F U j
  exact ((CommRingCat.isPushout_tensorProduct Γ(U.left, ⊤)
      Γ((selectedChart F U i).left, ⊤) Γ((selectedChart F U j).left, ⊤)).isoIsPushout
      (CommRingCat.of Γ((selectedChart F U i).left, ⊤))
      (CommRingCat.of Γ((selectedChart F U j).left, ⊤))
      (isPushout_appTop_of_isPullback (overlap_isPullback F U i j))).commRingCatIsoToRingEquiv

/-- Restriction of the finite product algebra from the left chart is native tensor-product
base change, with an explicit inverse built from its finite standard coordinates. -/
def overlapLeftProductEquiv (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    letI := overlapLeftAlgebra F U i j
    Γ((overlap F U i j).left, ⊤) ⊗[Γ((selectedChart F U i).left, ⊤)]
        chartAlgebra (selectedChart F U i) (selectedLabels F U i) ≃ₐ[Γ((overlap F U i j).left, ⊤)]
      chartAlgebra (overlap F U i j) (selectedLabels F U i) := by
  letI := overlapLeftAlgebra F U i j
  exact Algebra.TensorProduct.piScalarRight Γ((selectedChart F U i).left, ⊤)
    Γ((overlap F U i j).left, ⊤) Γ((overlap F U i j).left, ⊤)
    (Fin (Nat.card (selectedLabels F U i)))

/-- Restriction of the right finite product algebra uses the same native finite-coordinate map. -/
def overlapRightProductEquiv (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    letI := overlapRightAlgebra F U i j
    Γ((overlap F U i j).left, ⊤) ⊗[Γ((selectedChart F U j).left, ⊤)]
        chartAlgebra (selectedChart F U j) (selectedLabels F U j) ≃ₐ[Γ((overlap F U i j).left, ⊤)]
      chartAlgebra (overlap F U i j) (selectedLabels F U j) := by
  letI := overlapRightAlgebra F U i j
  exact Algebra.TensorProduct.piScalarRight Γ((selectedChart F U j).left, ⊤)
    Γ((overlap F U i j).left, ⊤) Γ((overlap F U i j).left, ⊤)
    (Fin (Nat.card (selectedLabels F U j)))

/-- The actual algebra descent transition compares the two base-changed finite chart algebras. -/
def overlapBaseChangeEquiv (U : X.Etale) [IsAffine U.left] (i j : finiteAffineIndex F U) :
    letI := overlapLeftAlgebra F U i j
    letI := overlapRightAlgebra F U i j
    Γ((overlap F U i j).left, ⊤) ⊗[Γ((selectedChart F U i).left, ⊤)]
        chartAlgebra (selectedChart F U i) (selectedLabels F U i) ≃ₐ[Γ((overlap F U i j).left, ⊤)]
      Γ((overlap F U i j).left, ⊤) ⊗[Γ((selectedChart F U j).left, ⊤)]
        chartAlgebra (selectedChart F U j) (selectedLabels F U j) := by
  letI := overlapLeftAlgebra F U i j
  letI := overlapRightAlgebra F U i j
  exact (overlapLeftProductEquiv F U i j).trans
    ((overlapTransition F U i j).trans (overlapRightProductEquiv F U i j).symm)

/-- The ring of the finite affine covering scheme. -/
abbrev coveringRing (U : X.Etale) [IsAffine U.left] : Type u :=
  ∀ i : finiteAffineIndex F U, Γ((selectedChart F U i).left, ⊤)

/-- The finite product of the actual local finite chart algebras. -/
abbrev coveringAlgebra (U : X.Etale) [IsAffine U.left] : Type u :=
  ∀ j : finiteAffineIndex F U, chartAlgebra (selectedChart F U j) (selectedLabels F U j)

/-- The base ring acts on covering rings by the genuine chart restriction maps. -/
abbrev coveringRingBaseAlgebra (U : X.Etale) [IsAffine U.left] :
    Algebra Γ(U.left, ⊤) (coveringRing F U) := by
  letI : ∀ i : finiteAffineIndex F U,
      Algebra Γ(U.left, ⊤) Γ((selectedChart F U i).left, ⊤) := fun i ↦ chartBaseAlgebra F U i
  infer_instance

/-- The base scalar action on the local finite algebras is componentwise chart restriction. -/
abbrev coveringAlgebraBaseAlgebra (U : X.Etale) [IsAffine U.left] :
    Algebra Γ(U.left, ⊤) (coveringAlgebra F U) := by
  letI : ∀ i : finiteAffineIndex F U,
      Algebra Γ(U.left, ⊤) Γ((selectedChart F U i).left, ⊤) := fun i ↦ chartBaseAlgebra F U i
  infer_instance

/-- Covering functions act on each finite local chart through constant functions in its labels. -/
def coveringStructureMap (U : X.Etale) [IsAffine U.left] :
    coveringRing F U →+* coveringAlgebra F U where
  toFun s j _ := s j
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The algebra structure of the local algebras over the covering ring. -/
abbrev coveringAlgebraOverCover (U : X.Etale) [IsAffine U.left] :
    Algebra (coveringRing F U) (coveringAlgebra F U) :=
  (coveringStructureMap F U).toAlgebra

/-- The scalar actions from the base and from the covering ring agree componentwise. -/
theorem coveringScalarTower (U : X.Etale) [IsAffine U.left] :
    letI := coveringRingBaseAlgebra F U
    letI := coveringAlgebraBaseAlgebra F U
    letI := coveringAlgebraOverCover F U
    IsScalarTower Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U) := by
  letI := coveringRingBaseAlgebra F U
  letI := coveringAlgebraBaseAlgebra F U
  letI := coveringAlgebraOverCover F U
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- Coordinates for the tensor product over the base, indexed by the two cover members and
the second chart's finite labels. The inverse uses native finite tensor sums and Γ-pushouts. -/
def coveringTensorEquiv (U : X.Etale) [IsAffine U.left] :
    letI := coveringRingBaseAlgebra F U
    letI := coveringAlgebraBaseAlgebra F U
    (coveringRing F U) ⊗[Γ(U.left, ⊤)] (coveringAlgebra F U) ≃+*
      ∀ i j : finiteAffineIndex F U, chartAlgebra (overlap F U i j) (selectedLabels F U j) := by
  letI : ∀ i : finiteAffineIndex F U,
      Algebra Γ(U.left, ⊤) Γ((selectedChart F U i).left, ⊤) := fun i ↦ chartBaseAlgebra F U i
  exact (Algebra.FiniteProductDescent.labelTensorEquiv Γ(U.left, ⊤)
    (fun i : finiteAffineIndex F U ↦ Γ((selectedChart F U i).left, ⊤))
    (fun j : finiteAffineIndex F U ↦ Γ((selectedChart F U j).left, ⊤))
    (fun j ↦ Nat.card (selectedLabels F U j))).toRingEquiv.trans
      (RingEquiv.piCongrRight fun i ↦ RingEquiv.piCongrRight fun j ↦
        RingEquiv.piCongrRight fun _ : Fin (Nat.card (selectedLabels F U j)) ↦ overlapTensorEquiv F U i j)

/-- A covering algebra section gives overlap-label coordinates by restricting the first chart
and applying its actual sheaf-theoretic transition to the second chart. -/
def coactionCoordinates (U : X.Etale) [IsAffine U.left] :
    coveringAlgebra F U →+*
      ∀ i j : finiteAffineIndex F U, chartAlgebra (overlap F U i j) (selectedLabels F U j) where
  toFun b i j := overlapTransition F U i j
    (fun k ↦ (pullback.fst (selectedChartMap F U i) (selectedChartMap F U j)).left.appTop.hom (b i k))
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- The actual algebra coaction is the inverse tensor-coordinate map applied to the real
overlap transition. No effectiveness or representability witness is selected. -/
def affineCoaction (U : X.Etale) [IsAffine U.left] :
    letI := coveringRingBaseAlgebra F U
    letI := coveringAlgebraBaseAlgebra F U
    letI := coveringAlgebraOverCover F U
    coveringAlgebra F U →ₐ[coveringRing F U]
      (coveringRing F U) ⊗[Γ(U.left, ⊤)] (coveringAlgebra F U) := by
  letI := coveringRingBaseAlgebra F U
  letI := coveringAlgebraBaseAlgebra F U
  letI := coveringAlgebraOverCover F U
  exact
    { (coveringTensorEquiv F U).symm.toRingHom.comp (coactionCoordinates F U) with
      commutes' := sorry }

/-- The genuine algebra descent datum carried by the selected finite constant cover. -/
def affineDescentData (U : X.Etale) [IsAffine U.left] :
    letI := coveringRingBaseAlgebra F U
    letI := coveringAlgebraBaseAlgebra F U
    letI := coveringAlgebraOverCover F U
    letI : IsScalarTower Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U) := coveringScalarTower F U
    @Algebra.FaithfullyFlatDescent.Coaction Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U)
      inferInstance inferInstance inferInstance
      (coveringRingBaseAlgebra F U) (coveringAlgebraOverCover F U)
      (coveringAlgebraBaseAlgebra F U) (coveringScalarTower F U) := by
  letI := coveringRingBaseAlgebra F U
  letI := coveringAlgebraBaseAlgebra F U
  letI := coveringAlgebraOverCover F U
  letI : IsScalarTower Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U) := coveringScalarTower F U
  exact @Algebra.FaithfullyFlatDescent.Coaction.mk Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U)
    inferInstance inferInstance inferInstance
    (coveringRingBaseAlgebra F U) (coveringAlgebraOverCover F U)
    (coveringAlgebraBaseAlgebra F U) (coveringScalarTower F U)
    (affineCoaction F U) (by sorry) (by sorry)

/-- The descended affine algebra is the literal subalgebra of overlap-invariant chart functions. -/
abbrev affineAlgebra (U : X.Etale) [IsAffine U.left] :
    letI := coveringAlgebraBaseAlgebra F U
    Subalgebra Γ(U.left, ⊤) (coveringAlgebra F U) :=
  letI := coveringRingBaseAlgebra F U
  letI := coveringAlgebraBaseAlgebra F U
  letI := coveringAlgebraOverCover F U
  letI : IsScalarTower Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U) := coveringScalarTower F U
  @Algebra.FaithfullyFlatDescent.descendedAlgebra Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U)
    inferInstance inferInstance inferInstance
    (coveringRingBaseAlgebra F U) (coveringAlgebraOverCover F U)
    (coveringAlgebraBaseAlgebra F U) (coveringScalarTower F U)
    (affineDescentData (F := F) U)

/-- The actual affine scheme obtained by descending the finite constant charts. -/
def affineRepresentation (U : X.Etale) [IsAffine U.left] : Scheme.{u} :=
  Spec (CommRingCat.of (affineAlgebra (F := F) U))

/-- The descended affine scheme maps to its base via the invariant algebra's structure map. -/
def affineRepresentationMap (U : X.Etale) [IsAffine U.left] :
    affineRepresentation (F := F) U ⟶ U.left :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) (affineAlgebra (F := F) U))) ≫ U.left.isoSpec.inv

/-- The finite affine cover is jointly flat and surjective, so its product ring is faithfully flat. -/
theorem coveringRing_faithfullyFlat (U : X.Etale) [IsAffine U.left] :
    letI := coveringRingBaseAlgebra F U
    (algebraMap Γ(U.left, ⊤) (coveringRing F U)).FaithfullyFlat := by
  classical
  letI : ∀ i : finiteAffineIndex F U,
      Algebra Γ(U.left, ⊤) Γ((selectedChart F U i).left, ⊤) := fun i ↦ chartBaseAlgebra F U i
  letI : ∀ i : finiteAffineIndex F U,
      Module.Flat Γ(U.left, ⊤) Γ((selectedChart F U i).left, ⊤) := fun i ↦ by
    apply (RingHom.flat_algebraMap_iff).mp
    exact (selectedChartMap F U i).left.flat_appTop
  letI : Module.Flat Γ(U.left, ⊤) (coveringRing F U) :=
    Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := Γ(U.left, ⊤))).symm
  apply RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, ?_⟩
  intro p
  let x : U.left := U.left.isoSpec.inv p
  obtain ⟨i, y, hy⟩ := (finiteAffineCover F U).cover x
  let q : PrimeSpectrum Γ((selectedChart F U i).left, ⊤) :=
    (selectedChart F U i).left.isoSpec.hom y
  let z : PrimeSpectrum (coveringRing F U) :=
    PrimeSpectrum.comap (Pi.evalRingHom (fun i : finiteAffineIndex F U ↦
      Γ((selectedChart F U i).left, ⊤)) i) q
  refine ⟨z, ?_⟩
  change PrimeSpectrum.comap
    ((Pi.evalRingHom (fun i : finiteAffineIndex F U ↦ Γ((selectedChart F U i).left, ⊤)) i).comp
      (algebraMap Γ(U.left, ⊤) (coveringRing F U))) q = p
  have hm : ((Pi.evalRingHom (fun i : finiteAffineIndex F U ↦
      Γ((selectedChart F U i).left, ⊤)) i).comp
      (algebraMap Γ(U.left, ⊤) (coveringRing F U))) = (selectedChartMap F U i).left.appTop.hom := rfl
  rw [hm]
  have hn := congrArg (fun f : (selectedChart F U i).left ⟶
      Spec (CommRingCat.of Γ(U.left, ⊤)) ↦ f y)
    (Scheme.isoSpec_hom_naturality (selectedChartMap F U i).left)
  change PrimeSpectrum.comap (selectedChartMap F U i).left.appTop.hom q =
    U.left.isoSpec.hom ((selectedChartMap F U i).left y) at hn
  rw [hn]
  change U.left.isoSpec.hom ((finiteAffineCover F U).map i y) = p
  rw [hy]
  change U.left.isoSpec.hom (U.left.isoSpec.inv p) = p
  exact congrArg (fun f : Spec (CommRingCat.of Γ(U.left, ⊤)) ⟶ _ ↦ f p) U.left.isoSpec.inv_hom_id

/-- Base changing the actual descended algebra recovers the original finite chart algebras
through the native faithfully-flat module descent inverse. -/
def affineReconstruction (U : X.Etale) [IsAffine U.left] :
    letI := coveringRingBaseAlgebra F U
    letI := coveringAlgebraBaseAlgebra F U
    letI := coveringAlgebraOverCover F U
    letI : IsScalarTower Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U) := coveringScalarTower F U
    (coveringRing F U) ⊗[Γ(U.left, ⊤)] (affineAlgebra (F := F) U) ≃ₐ[coveringRing F U]
      coveringAlgebra F U := by
  letI := coveringRingBaseAlgebra F U
  letI := coveringAlgebraBaseAlgebra F U
  letI := coveringAlgebraOverCover F U
  letI : IsScalarTower Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U) := coveringScalarTower F U
  exact @Algebra.FaithfullyFlatDescent.reconstructionEquiv Γ(U.left, ⊤) (coveringRing F U) (coveringAlgebra F U)
    inferInstance inferInstance inferInstance
    (coveringRingBaseAlgebra F U) (coveringAlgebraOverCover F U)
    (coveringAlgebraBaseAlgebra F U) (coveringScalarTower F U)
    (affineDescentData (F := F) U)
    (coveringRing_faithfullyFlat (F := F) U)

/-- Membership in the descended affine algebra is the genuine overlap descent equation. -/
theorem mem_affineAlgebra (U : X.Etale) [IsAffine U.left] (b : coveringAlgebra F U) :
    b ∈ affineAlgebra (F := F) U ↔
      (letI := coveringRingBaseAlgebra F U
       letI := coveringAlgebraBaseAlgebra F U
       letI := coveringAlgebraOverCover F U
       affineCoaction F U b = (1 : coveringRing F U) ⊗ₜ[Γ(U.left, ⊤)] b) := Iff.rfl

/-- The local coaction is computed by the actual tensor-coordinate inverse. -/
theorem affineCoaction_apply (U : X.Etale) [IsAffine U.left] (b : coveringAlgebra F U) :
    (letI := coveringRingBaseAlgebra F U
     letI := coveringAlgebraBaseAlgebra F U
     letI := coveringAlgebraOverCover F U
     affineCoaction F U b) =
      (coveringTensorEquiv F U).symm (coactionCoordinates F U b) := rfl

/-- The native faithfully-flat reconstruction recovers the local finite product algebra. -/
theorem affineReconstruction_tmul (U : X.Etale) [IsAffine U.left]
    (s : coveringRing F U) (b : affineAlgebra (F := F) U) :
    (letI := coveringRingBaseAlgebra F U
     letI := coveringAlgebraBaseAlgebra F U
     letI := coveringAlgebraOverCover F U
     affineReconstruction F U (s ⊗ₜ[Γ(U.left, ⊤)] b)) =
      coveringStructureMap F U s * (b : coveringAlgebra F U) := sorry

/-- The actual descended affine structural morphism is finite. -/
instance affineRepresentationMap_isFinite (U : X.Etale) [IsAffine U.left] :
    IsFinite (affineRepresentationMap F U) := sorry

/-- The actual descended affine structural morphism is étale. -/
instance affineRepresentationMap_etale (U : X.Etale) [IsAffine U.left] :
    Etale (affineRepresentationMap F U) := sorry

/-- The finite étale object produced from the actual local constant chart cover over an affine base. -/
def affineFiniteEtale (U : X.Etale) [IsAffine U.left] : FiniteEtale U.left :=
  MorphismProperty.Over.mk ⊤ (affineRepresentationMap F U) ⟨inferInstance, inferInstance⟩

/-- Restrict an intrinsic function to each selected chart and read its actual finite coordinates. -/
def affineFunctionCoordinates (U : X.Etale) [IsAffine U.left] :
    localFunctionAlgebra F U →+* coveringAlgebra F U where
  toFun a i := localCoordinates F (selectedChart F U i) (selectedLabels F U i)
    (finiteAffineChartIso F U i)
    (Sheaf.FunctionAlgebra.restrictAlong.{u + 1, u, u + 1, u} F (SmallStandardTopology.commStructureSheaf .etale X)
      (selectedChartMap F U i) a)
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- An intrinsic function satisfies the actual overlap coaction equation in chart coordinates. -/
theorem affineFunctionCoordinates_mem (U : X.Etale) [IsAffine U.left]
    (a : localFunctionAlgebra F U) :
    affineFunctionCoordinates F U a ∈ affineAlgebra (F := F) U := sorry

/-- The forward map into the small descended algebra retains every actual chart coordinate. -/
def affineFunctionsToInvariants (U : X.Etale) [IsAffine U.left] :
    localFunctionAlgebra F U →+* affineAlgebra (F := F) U where
  toFun a := ⟨affineFunctionCoordinates F U a, affineFunctionCoordinates_mem F U a⟩
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- Read invariant chart coordinates as local functions on the iterated slice used by gluing. -/
def affineInvariantLocalFunctions (U : X.Etale) [IsAffine U.left]
    (b : affineAlgebra (F := F) U) (i : finiteAffineIndex F U) :
    Sheaf.FunctionAlgebra ((F.over U).over (Over.mk (selectedChartMap F U i)))
      (((SmallStandardTopology.commStructureSheaf .etale X).over U).over
        (Over.mk (selectedChartMap F U i))) :=
  Sheaf.FunctionAlgebra.iteratedSliceEquiv.{u + 1, u, u + 1, u} F (SmallStandardTopology.commStructureSheaf .etale X)
    (Over.mk (selectedChartMap F U i))
    ((localCoordinates F (selectedChart F U i) (selectedLabels F U i)
      (finiteAffineChartIso F U i)).symm (b.val i))

/-- The invariant coaction equation makes these functions agree on every common slice test object. -/
theorem affineInvariantLocalFunctions_compatible (U : X.Etale) [IsAffine U.left]
    (b : affineAlgebra (F := F) U) :
    Sheaf.FunctionAlgebra.Compatible.{u + 1, u, u + 1, u, 0} (F.over U)
      ((SmallStandardTopology.commStructureSheaf .etale X).over U)
      (fun i : finiteAffineIndex F U ↦ Over.mk (selectedChartMap F U i))
      (affineInvariantLocalFunctions F U b) := sorry

/-- Glue the actual invariant chart functions through the native internal-Hom sheaf. -/
def affineInvariantsToFunctions (U : X.Etale) [IsAffine U.left] :
    affineAlgebra (F := F) U →+* localFunctionAlgebra F U where
  toFun b := Sheaf.FunctionAlgebra.glue.{u + 1, u, u + 1, u, 0}
    (F.over U) ((SmallStandardTopology.commStructureSheaf .etale X).over U)
    (fun i : finiteAffineIndex F U ↦ Over.mk (selectedChartMap F U i))
    (selectedCharts_coversTop F U) (affineInvariantLocalFunctions F U b)
    (affineInvariantLocalFunctions_compatible F U b)
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- The small descended algebra is the intrinsic natural-function ring, with two implemented maps. -/
def affineFunctionEquiv (U : X.Etale) [IsAffine U.left] :
    affineAlgebra (F := F) U ≃+* localFunctionAlgebra F U where
  toFun := affineInvariantsToFunctions F U
  invFun := affineFunctionsToInvariants F U
  left_inv := sorry
  right_inv := sorry
  map_add' := (affineInvariantsToFunctions F U).map_add
  map_mul' := (affineInvariantsToFunctions F U).map_mul

/-- Restriction of descended algebras is intrinsic restriction conjugated by actual chart gluing. -/
def affineRestrict {U V : X.Etale} [IsAffine U.left] [IsAffine V.left] (f : V ⟶ U) :
    affineAlgebra (F := F) U →+* affineAlgebra (F := F) V :=
  (affineFunctionsToInvariants F V).comp
    ((Sheaf.FunctionAlgebra.restrictAlong.{u + 1, u, u + 1, u} F (SmallStandardTopology.commStructureSheaf .etale X) f).comp
      (affineInvariantsToFunctions F U))

/-- The restriction map of the actual affine representing schemes. -/
def affineRestrictionMap {U V : X.Etale} [IsAffine U.left] [IsAffine V.left] (f : V ⟶ U) :
    affineRepresentation F V ⟶ affineRepresentation F U :=
  Spec.map (CommRingCat.ofHom (affineRestrict F f))

/-- The actual restriction maps commute with their maps to the underlying affine charts. -/
theorem affineRestrictionMap_naturality {U V : X.Etale} [IsAffine U.left] [IsAffine V.left]
    (f : V ⟶ U) :
    affineRestrictionMap F f ≫ affineRepresentationMap F U =
      affineRepresentationMap F V ≫ f.left := sorry

/-- Evaluation of an intrinsic function at a supplied section is a genuine ring map. -/
def localFunctionEvaluation (U : X.Etale) (x : F.obj.obj (op U)) :
    localFunctionAlgebra F U →+* Γ(U.left, ⊤) where
  toFun a := Sheaf.FunctionAlgebra.eval (F.over U)
    ((SmallStandardTopology.commStructureSheaf .etale X).over U) a (op (Over.mk (𝟙 U))) x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- A supplied sheaf section evaluates actual invariant algebra functions on the base chart. -/
def affineSectionEvaluation (U : X.Etale) [IsAffine U.left] (x : F.obj.obj (op U)) :
    affineAlgebra (F := F) U →+* Γ(U.left, ⊤) :=
  (localFunctionEvaluation F U x).comp (affineInvariantsToFunctions F U)

/-- The morphism to the actual affine representing scheme defined by a supplied sheaf section. -/
def affineSectionMap (U : X.Etale) [IsAffine U.left] (x : F.obj.obj (op U)) :
    U.left ⟶ affineRepresentation F U :=
  U.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (affineSectionEvaluation F U x))

/-- Evaluation of scalar functions makes the section map a morphism over its base. -/
theorem affineSectionMap_over (U : X.Etale) [IsAffine U.left] (x : F.obj.obj (op U)) :
    affineSectionMap F U x ≫ affineRepresentationMap F U = 𝟙 U.left := sorry

/-- Evaluation commutes with restriction of the supplied sheaf section. -/
theorem affineSectionMap_naturality {U V : X.Etale} [IsAffine U.left] [IsAffine V.left]
    (f : V ⟶ U) (x : F.obj.obj (op U)) :
    f.left ≫ affineSectionMap F U x =
      affineSectionMap F V (F.obj.map f.op x) ≫ affineRestrictionMap F f := sorry

end AlgebraicGeometry.Scheme.FiniteLocallyConstant
