/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexed Graded-Piece Columns of a Filtered Complex

For a filtered cochain complex, fixing a filtration degree gives a cochain complex whose
degree-`q` object is the degree-`p + q` object of the `p`-th graded piece. This file owns that
reindexing, its functoriality, and its homology comparison independently of any chosen spectral
sequence realization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]

namespace FilteredComplex

/-- The differential of a graded-piece column vanishes outside the reindexed cochain shape. -/
theorem GradedPiece.Column.shape (K : FilteredComplex C) (p q q' : ℤ)
    (hqq' : ¬ (ComplexShape.up ℤ).Rel q q') :
    (K.gradedPiece p).d (p + q) (p + q') = 0 := by
  apply (K.gradedPiece p).shape
  intro h
  apply hqq'
  change q + 1 = q'
  change (p + q) + 1 = p + q' at h
  exact add_left_cancel (by simpa only [add_assoc] using h)

/-- Two successive differentials in a reindexed graded-piece column compose to zero. -/
theorem GradedPiece.Column.d_comp_d (K : FilteredComplex C) (p q q' q'' : ℤ)
    (hqq' : (ComplexShape.up ℤ).Rel q q')
    (hq'q'' : (ComplexShape.up ℤ).Rel q' q'') :
    (K.gradedPiece p).d (p + q) (p + q') ≫
      (K.gradedPiece p).d (p + q') (p + q'') = 0 := by
  exact (K.gradedPiece p).d_comp_d _ _ _

/-- The `p`-th graded-piece complex, reindexed so that bidegree `(p,q)` has total degree
`p + q`. -/
@[stacks 012M "reindexed graded-piece column"]
def GradedPiece.Column.complex (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ where
  X q := (K.gradedPiece p).X (p + q)
  d q q' := (K.gradedPiece p).d (p + q) (p + q')
  shape q q' hqq' := GradedPiece.Column.shape K p q q' hqq'
  d_comp_d' q q' q'' hqq' hq'q'' :=
    GradedPiece.Column.d_comp_d K p q q' q'' hqq' hq'q''

/-- The componentwise map on a reindexed graded-piece column commutes with its differentials. -/
@[reassoc, stacks 012M "naturality of the graded-piece column differential"]
theorem GradedPiece.Column.map_comm {K L : FilteredComplex C}
    (α : K ⟶ L) (p q q' : ℤ) (hqq' : (ComplexShape.up ℤ).Rel q q') :
    (gradedPieceMap α p).f (p + q) ≫ (GradedPiece.Column.complex L p).d q q' =
      (GradedPiece.Column.complex K p).d q q' ≫ (gradedPieceMap α p).f (p + q') := by
  exact (gradedPieceMap α p).comm _ _

/-- The morphism on a fixed reindexed graded-piece column induced by a filtered-complex
morphism. -/
noncomputable def GradedPiece.Column.map {K L : FilteredComplex C}
    (α : K ⟶ L) (p : ℤ) : GradedPiece.Column.complex K p ⟶ GradedPiece.Column.complex L p where
  f q := (gradedPieceMap α p).f (p + q)
  comm' q q' hqq' := GradedPiece.Column.map_comm α p q q' hqq'

/-- The fixed graded-piece column map of an identity is the identity. -/
@[simp, stacks 012M "identity map of a graded-piece column"]
theorem GradedPiece.Column.map_id (K : FilteredComplex C) (p : ℤ) :
    GradedPiece.Column.map (𝟙 K) p = 𝟙 (GradedPiece.Column.complex K p) := by
  ext q
  exact congrArg (fun f ↦ f.f (p + q)) ((gradedPieceFunctor p).map_id K)

/-- Fixed graded-piece column maps preserve composition. -/
@[simp, stacks 012M "composition of graded-piece column maps"]
theorem GradedPiece.Column.map_comp {K L M : FilteredComplex C}
    (α : K ⟶ L) (β : L ⟶ M) (p : ℤ) :
    GradedPiece.Column.map (α ≫ β) p = GradedPiece.Column.map α p ≫
      GradedPiece.Column.map β p := by
  ext q
  exact congrArg (fun f ↦ f.f (p + q)) ((gradedPieceFunctor p).map_comp α β)

/-- Fixing the filtration index makes the reindexed graded-piece construction functorial. -/
noncomputable def GradedPiece.Column.functor (p : ℤ) :
    FilteredComplex C ⥤ CochainComplex C ℤ where
  obj K := GradedPiece.Column.complex K p
  map α := GradedPiece.Column.map α p
  map_id K := GradedPiece.Column.map_id K p
  map_comp α β := GradedPiece.Column.map_comp α β p

/-- The short complex around `q` in a reindexed graded-piece column is the short complex around
total degree `p + q` in the graded-piece complex. -/
noncomputable def GradedPiece.Column.scIso (K : FilteredComplex C) (p q : ℤ) :
    (GradedPiece.Column.complex K p).sc' (q - 1) q (q + 1) ≅
      (K.gradedPiece p).sc' (p + (q - 1)) (p + q) (p + (q + 1)) :=
  Iso.refl _

/-- The reindexed predecessor total degree is related to the central total degree. -/
theorem GradedPiece.Column.prev_rel (p q : ℤ) :
    (ComplexShape.up ℤ).Rel (p + (q - 1)) (p + q) := by
  change (p + (q - 1)) + 1 = p + q
  simp [add_assoc]

/-- The central total degree is related to its reindexed successor. -/
theorem GradedPiece.Column.next_rel (p q : ℤ) :
    (ComplexShape.up ℤ).Rel (p + q) (p + (q + 1)) := by
  exact add_assoc p q 1

section Homology

variable [CategoryWithHomology C]

omit [HasCokernels C] in
private theorem GradedPiece.Column.homologyIsoSc'_hom_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (i j k : ℤ)
    (hi : (ComplexShape.up ℤ).prev j = i) (hk : (ComplexShape.up ℤ).next j = k) :
    HomologicalComplex.homologyMap f j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ) i j k).map f) := by
  change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) j).map f) ≫
        ShortComplex.homologyMap (L.isoSc' i j k hi hk).hom =
      ShortComplex.homologyMap (K.isoSc' i j k hi hk).hom ≫ _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  exact congrArg (fun φ ↦ ShortComplex.homologyMap φ)
    ((HomologicalComplex.natIsoSc' C (ComplexShape.up ℤ) i j k hi hk).hom.naturality f)

/-- Homology of a reindexed graded-piece column agrees with graded-piece homology in total
degree `p + q`. -/
@[stacks 012M "homology of a reindexed graded-piece column"]
noncomputable def GradedPiece.Column.homologyIso (K : FilteredComplex C) (p q : ℤ) :
    (GradedPiece.Column.complex K p).homology q ≅ (K.gradedPiece p).homology (p + q) :=
  (GradedPiece.Column.complex K p).homologyIsoSc' (q - 1) q (q + 1)
      (CochainComplex.prev ℤ q) (CochainComplex.next ℤ q) ≪≫
    ShortComplex.homologyMapIso (GradedPiece.Column.scIso K p q) ≪≫
    ((K.gradedPiece p).homologyIsoSc' (p + (q - 1)) (p + q) (p + (q + 1))
      (ComplexShape.prev_eq' (ComplexShape.up ℤ)
        (GradedPiece.Column.prev_rel p q))
      (ComplexShape.next_eq' (ComplexShape.up ℤ)
        (GradedPiece.Column.next_rel p q))).symm

/-- The graded-piece column homology comparison is natural in filtered-complex morphisms. -/
@[reassoc, stacks 012M "naturality of graded-piece column homology"]
theorem GradedPiece.Column.homologyIso_hom_naturality
    {K L : FilteredComplex C} (α : K ⟶ L) (p q : ℤ) :
    HomologicalComplex.homologyMap (GradedPiece.Column.map α p) q ≫
        (GradedPiece.Column.homologyIso L p q).hom =
      (GradedPiece.Column.homologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q) := by
  let eK : (GradedPiece.Column.complex K p).homology q ≅
      ((K.gradedPiece p).sc' (p + (q - 1)) (p + q) (p + (q + 1))).homology :=
    (GradedPiece.Column.complex K p).homologyIsoSc' (q - 1) q (q + 1)
      (CochainComplex.prev ℤ q) (CochainComplex.next ℤ q)
  let eL : (GradedPiece.Column.complex L p).homology q ≅
      ((L.gradedPiece p).sc' (p + (q - 1)) (p + q) (p + (q + 1))).homology :=
    (GradedPiece.Column.complex L p).homologyIsoSc' (q - 1) q (q + 1)
      (CochainComplex.prev ℤ q) (CochainComplex.next ℤ q)
  let eK' := (K.gradedPiece p).homologyIsoSc' (p + (q - 1)) (p + q) (p + (q + 1))
    (ComplexShape.prev_eq' _ (GradedPiece.Column.prev_rel p q))
    (ComplexShape.next_eq' _ (GradedPiece.Column.next_rel p q))
  let eL' := (L.gradedPiece p).homologyIsoSc' (p + (q - 1)) (p + q) (p + (q + 1))
    (ComplexShape.prev_eq' _ (GradedPiece.Column.prev_rel p q))
    (ComplexShape.next_eq' _ (GradedPiece.Column.next_rel p q))
  let f := (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ)
    (p + (q - 1)) (p + q) (p + (q + 1))).map (gradedPieceMap α p)
  have hcol : HomologicalComplex.homologyMap (GradedPiece.Column.map α p) q ≫ eL.hom =
      eK.hom ≫ ShortComplex.homologyMap f :=
    GradedPiece.Column.homologyIsoSc'_hom_naturality _ _ _ _ _ _
  have hgr : HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q) ≫ eL'.hom =
      eK'.hom ≫ ShortComplex.homologyMap f :=
    GradedPiece.Column.homologyIsoSc'_hom_naturality _ _ _ _ _ _
  change HomologicalComplex.homologyMap (GradedPiece.Column.map α p) q ≫
      (eL.hom ≫ ShortComplex.homologyMap (𝟙 _) ≫ eL'.inv) =
    (eK.hom ≫ ShortComplex.homologyMap (𝟙 _) ≫ eK'.inv) ≫
      HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q)
  simp only [ShortComplex.homologyMap_id, Category.id_comp]
  apply (cancel_mono eL'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hcol, hgr, Iso.inv_hom_id_assoc]

/-- The inverse graded-piece column homology comparison is natural in filtered-complex
morphisms. -/
@[reassoc, stacks 012M "inverse naturality of graded-piece column homology"]
theorem GradedPiece.Column.homologyIso_inv_naturality
    {K L : FilteredComplex C} (α : K ⟶ L) (p q : ℤ) :
    HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q) ≫
        (GradedPiece.Column.homologyIso L p q).inv =
      (GradedPiece.Column.homologyIso K p q).inv ≫
        HomologicalComplex.homologyMap (GradedPiece.Column.map α p) q := by
  apply (cancel_mono (GradedPiece.Column.homologyIso L p q).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [GradedPiece.Column.homologyIso_hom_naturality,
    Iso.inv_hom_id_assoc]

/-- Conjugating a graded-piece homology map by the column comparisons recovers the column
homology map. -/
@[reassoc, stacks 012M "computation of graded-piece column homology"]
theorem GradedPiece.Column.homologyIso_naturality_inv
    {K L : FilteredComplex C} (α : K ⟶ L) (p q : ℤ) :
    (GradedPiece.Column.homologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (gradedPieceMap α p) (p + q) ≫
        (GradedPiece.Column.homologyIso L p q).inv =
      HomologicalComplex.homologyMap (GradedPiece.Column.map α p) q := by
  rw [← GradedPiece.Column.homologyIso_hom_naturality_assoc, Iso.hom_inv_id,
    Category.comp_id]

end Homology

end FilteredComplex
end CategoryTheory
