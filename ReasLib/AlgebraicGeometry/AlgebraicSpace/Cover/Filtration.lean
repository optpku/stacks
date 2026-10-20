/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# Finite nested closed filtrations with finite scheme covers

This file owns terminating nested closed subspaces of an algebraic space,
each of finite presentation over the ambient space, together with scheme
covers that are surjective, finite, and of finite presentation, and finite
étale over the successive differences.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The point-set of the successive difference `Z_i \ Z_{i+1}` associated to a
sequence of closed subspaces, as a subset of `Points X`. -/
def closedStratumPoints {t : ℕ} (Z : Fin (t + 1) → ClosedSubspace X) (i : Fin t) :
    Set (Points X) :=
  (Z i.castSucc).pointsSet \ (Z i.succ).pointsSet

/-- Membership in `closedStratumPoints Z i` means the point lies in the `i`-th
closed stage and not in the next one. -/
theorem mem_closedStratumPoints {t : ℕ} (Z : Fin (t + 1) → ClosedSubspace X)
    (i : Fin t) {x : Points X} :
    x ∈ closedStratumPoints Z i ↔
      x ∈ (Z i.castSucc).pointsSet ∧ x ∉ (Z i.succ).pointsSet :=
  sorry

/-- The inverse image of `closedStratumPoints Z i` in `|Z_i|`, as a subset of
`Points (Z i.castSucc).X`. -/
def closedStratumOpenPoints {t : ℕ} (Z : Fin (t + 1) → ClosedSubspace X) (i : Fin t) :
    Set (Points (Z i.castSucc).X) :=
  Points.map (Z i.castSucc).ι ⁻¹' closedStratumPoints Z i

/-- Membership in `closedStratumOpenPoints Z i` means the image in `|X|` lies in
the successive difference `Z_i \ Z_{i+1}`. -/
theorem mem_closedStratumOpenPoints {t : ℕ} (Z : Fin (t + 1) → ClosedSubspace X)
    (i : Fin t) {x : Points (Z i.castSucc).X} :
    x ∈ closedStratumOpenPoints Z i ↔
      Points.map (Z i.castSucc).ι x ∈ closedStratumPoints Z i :=
  sorry

/-- A terminating nested sequence of closed subspaces of `X`, each of finite
presentation over `X`, with first stage a thickening and last stage empty,
together with scheme covers that are surjective, finite, and of finite
presentation, and finite étale over the successive differences. -/
structure FiniteClosedSchemeCoverFiltration (X : AlgebraicSpace S) where
  /-- An index `t` such that the last closed stage is empty. -/
  bound : ℕ
  /-- The nested closed subspaces `Z_0, …, Z_t`. -/
  closedStage : Fin (bound + 1) → ClosedSubspace X
  /-- The covering scheme `Y_i` of the `i`-th closed stage. -/
  schemeStage : Fin bound → AlgebraicSpace S
  /-- The cover morphism `Y_i ⟶ Z_i`. -/
  cover (i : Fin bound) : schemeStage i ⟶ (closedStage i.castSucc).X
  /-- An open subspace of `Z_i` representing the difference `Z_i \ Z_{i+1}`. -/
  diffOpen (i : Fin bound) : OpenSubspace (closedStage i.castSucc).X
  /-- The scheme-theoretic inclusion `Z_{i+1} ⟶ Z_i` of successive closed stages. -/
  stageIncl (i : Fin bound) : (closedStage i.succ).X ⟶ (closedStage i.castSucc).X
  /-- Each successive inclusion is a closed immersion. -/
  isClosedImmersion_stageIncl (i : Fin bound) : IsClosedImmersion (stageIncl i)
  /-- The inclusion `Z_{i+1} ⟶ Z_i` lies over `X`, recovering `Z_i ⊃ Z_{i+1}`. -/
  stageIncl_ι (i : Fin bound) :
    stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι
  /-- Support nesting `|Z_0| ⊃ ⋯ ⊃ |Z_t|`, implied by the scheme-theoretic
  inclusions. -/
  antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet
  /-- Each closed immersion `Z_i ⟶ X` is of finite presentation. -/
  finitePresentation_closedStage (i : Fin (bound + 1)) :
    FinitePresentation (closedStage i).ι
  /-- The inclusion of the first closed stage is a thickening. -/
  isThickening_zero : IsThickening (closedStage 0).ι
  /-- The last closed stage occupies none of `|X|`, encoding `Z_t = ∅`. -/
  pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅
  /-- Each covering space `Y_i` is a scheme. -/
  isScheme_schemeStage (i : Fin bound) : IsScheme (schemeStage i)
  /-- Each cover `Y_i ⟶ Z_i` is finite. -/
  isFinite_cover (i : Fin bound) : IsFinite (cover i)
  /-- Each cover `Y_i ⟶ Z_i` is of finite presentation. -/
  finitePresentation_cover (i : Fin bound) : FinitePresentation (cover i)
  /-- Each cover `Y_i ⟶ Z_i` is surjective. -/
  surjective_cover (i : Fin bound) : Surjective (cover i)
  /-- The stored open of `Z_i` occupies the successive difference `Z_i \ Z_{i+1}`. -/
  diffOpen_pointsSet (i : Fin bound) :
    (diffOpen i).pointsSet = closedStratumOpenPoints closedStage i
  /-- The restriction of `Y_i ⟶ Z_i` to `Z_i \ Z_{i+1}` is finite. -/
  isFinite_cover_diffOpen (i : Fin bound) :
    IsFinite (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf)
  /-- The restriction of `Y_i ⟶ Z_i` to `Z_i \ Z_{i+1}` is étale. -/
  etale_cover_diffOpen (i : Fin bound) :
    Etale (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf)

namespace FiniteClosedSchemeCoverFiltration

/-- Assemble a finite closed scheme-cover filtration from nested closed stages,
scheme-theoretic inclusions, scheme covers, difference opens, and their geometric laws. -/
def ofStages {X : AlgebraicSpace S} (bound : ℕ)
    (closedStage : Fin (bound + 1) → ClosedSubspace X)
    (schemeStage : Fin bound → AlgebraicSpace S)
    (cover : ∀ i, schemeStage i ⟶ (closedStage i.castSucc).X)
    (diffOpen : ∀ i, OpenSubspace (closedStage i.castSucc).X)
    (stageIncl : ∀ i : Fin bound, (closedStage i.succ).X ⟶ (closedStage i.castSucc).X)
    (isClosedImmersion_stageIncl : ∀ i, IsClosedImmersion (stageIncl i))
    (stageIncl_ι :
      ∀ i : Fin bound, stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι)
    (antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet)
    (finitePresentation_closedStage : ∀ i, FinitePresentation (closedStage i).ι)
    (isThickening_zero : IsThickening (closedStage 0).ι)
    (pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅)
    (isScheme_schemeStage : ∀ i, IsScheme (schemeStage i))
    (isFinite_cover : ∀ i, IsFinite (cover i))
    (finitePresentation_cover : ∀ i, FinitePresentation (cover i))
    (surjective_cover : ∀ i, Surjective (cover i))
    (diffOpen_pointsSet :
      ∀ i, (diffOpen i).pointsSet = closedStratumOpenPoints closedStage i)
    (isFinite_cover_diffOpen :
      ∀ i, IsFinite (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf))
    (etale_cover_diffOpen :
      ∀ i, Etale (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf)) :
    FiniteClosedSchemeCoverFiltration X where
  bound := bound
  closedStage := closedStage
  schemeStage := schemeStage
  cover := cover
  diffOpen := diffOpen
  stageIncl := stageIncl
  isClosedImmersion_stageIncl := isClosedImmersion_stageIncl
  stageIncl_ι := stageIncl_ι
  antitone_pointsSet := antitone_pointsSet
  finitePresentation_closedStage := finitePresentation_closedStage
  isThickening_zero := isThickening_zero
  pointsSet_last := pointsSet_last
  isScheme_schemeStage := isScheme_schemeStage
  isFinite_cover := isFinite_cover
  finitePresentation_cover := finitePresentation_cover
  surjective_cover := surjective_cover
  diffOpen_pointsSet := diffOpen_pointsSet
  isFinite_cover_diffOpen := isFinite_cover_diffOpen
  etale_cover_diffOpen := etale_cover_diffOpen

/-- The bound of a filtration built by `ofStages` is the supplied bound. -/
@[simp]
theorem ofStages_bound {X : AlgebraicSpace S} (bound : ℕ)
    (closedStage : Fin (bound + 1) → ClosedSubspace X)
    (schemeStage : Fin bound → AlgebraicSpace S)
    (cover : ∀ i, schemeStage i ⟶ (closedStage i.castSucc).X)
    (diffOpen : ∀ i, OpenSubspace (closedStage i.castSucc).X)
    (stageIncl : ∀ i : Fin bound, (closedStage i.succ).X ⟶ (closedStage i.castSucc).X)
    (isClosedImmersion_stageIncl : ∀ i, IsClosedImmersion (stageIncl i))
    (stageIncl_ι :
      ∀ i : Fin bound, stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι)
    (antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet)
    (finitePresentation_closedStage : ∀ i, FinitePresentation (closedStage i).ι)
    (isThickening_zero : IsThickening (closedStage 0).ι)
    (pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅)
    (isScheme_schemeStage : ∀ i, IsScheme (schemeStage i))
    (isFinite_cover : ∀ i, IsFinite (cover i))
    (finitePresentation_cover : ∀ i, FinitePresentation (cover i))
    (surjective_cover : ∀ i, Surjective (cover i))
    (diffOpen_pointsSet :
      ∀ i, (diffOpen i).pointsSet = closedStratumOpenPoints closedStage i)
    (isFinite_cover_diffOpen :
      ∀ i, IsFinite (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf))
    (etale_cover_diffOpen :
      ∀ i, Etale (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf)) :
    (ofStages bound closedStage schemeStage cover diffOpen stageIncl
        isClosedImmersion_stageIncl stageIncl_ι
        antitone_pointsSet finitePresentation_closedStage isThickening_zero
        pointsSet_last isScheme_schemeStage isFinite_cover finitePresentation_cover
        surjective_cover diffOpen_pointsSet isFinite_cover_diffOpen
        etale_cover_diffOpen).bound =
      bound :=
  sorry

/-- The closed stages of a filtration built by `ofStages` are the supplied stages. -/
@[simp]
theorem ofStages_closedStage {X : AlgebraicSpace S} (bound : ℕ)
    (closedStage : Fin (bound + 1) → ClosedSubspace X)
    (schemeStage : Fin bound → AlgebraicSpace S)
    (cover : ∀ i, schemeStage i ⟶ (closedStage i.castSucc).X)
    (diffOpen : ∀ i, OpenSubspace (closedStage i.castSucc).X)
    (stageIncl : ∀ i : Fin bound, (closedStage i.succ).X ⟶ (closedStage i.castSucc).X)
    (isClosedImmersion_stageIncl : ∀ i, IsClosedImmersion (stageIncl i))
    (stageIncl_ι :
      ∀ i : Fin bound, stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι)
    (antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet)
    (finitePresentation_closedStage : ∀ i, FinitePresentation (closedStage i).ι)
    (isThickening_zero : IsThickening (closedStage 0).ι)
    (pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅)
    (isScheme_schemeStage : ∀ i, IsScheme (schemeStage i))
    (isFinite_cover : ∀ i, IsFinite (cover i))
    (finitePresentation_cover : ∀ i, FinitePresentation (cover i))
    (surjective_cover : ∀ i, Surjective (cover i))
    (diffOpen_pointsSet :
      ∀ i, (diffOpen i).pointsSet = closedStratumOpenPoints closedStage i)
    (isFinite_cover_diffOpen :
      ∀ i, IsFinite (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf))
    (etale_cover_diffOpen :
      ∀ i, Etale (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf)) :
    (ofStages bound closedStage schemeStage cover diffOpen stageIncl
        isClosedImmersion_stageIncl stageIncl_ι
        antitone_pointsSet finitePresentation_closedStage isThickening_zero
        pointsSet_last isScheme_schemeStage isFinite_cover finitePresentation_cover
        surjective_cover diffOpen_pointsSet isFinite_cover_diffOpen
        etale_cover_diffOpen).closedStage =
      closedStage :=
  sorry

/-- The covering schemes of a filtration built by `ofStages` are the supplied
schemes. -/
@[simp]
theorem ofStages_schemeStage {X : AlgebraicSpace S} (bound : ℕ)
    (closedStage : Fin (bound + 1) → ClosedSubspace X)
    (schemeStage : Fin bound → AlgebraicSpace S)
    (cover : ∀ i, schemeStage i ⟶ (closedStage i.castSucc).X)
    (diffOpen : ∀ i, OpenSubspace (closedStage i.castSucc).X)
    (stageIncl : ∀ i : Fin bound, (closedStage i.succ).X ⟶ (closedStage i.castSucc).X)
    (isClosedImmersion_stageIncl : ∀ i, IsClosedImmersion (stageIncl i))
    (stageIncl_ι :
      ∀ i : Fin bound, stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι)
    (antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet)
    (finitePresentation_closedStage : ∀ i, FinitePresentation (closedStage i).ι)
    (isThickening_zero : IsThickening (closedStage 0).ι)
    (pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅)
    (isScheme_schemeStage : ∀ i, IsScheme (schemeStage i))
    (isFinite_cover : ∀ i, IsFinite (cover i))
    (finitePresentation_cover : ∀ i, FinitePresentation (cover i))
    (surjective_cover : ∀ i, Surjective (cover i))
    (diffOpen_pointsSet :
      ∀ i, (diffOpen i).pointsSet = closedStratumOpenPoints closedStage i)
    (isFinite_cover_diffOpen :
      ∀ i, IsFinite (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf))
    (etale_cover_diffOpen :
      ∀ i, Etale (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf)) :
    (ofStages bound closedStage schemeStage cover diffOpen stageIncl
        isClosedImmersion_stageIncl stageIncl_ι
        antitone_pointsSet finitePresentation_closedStage isThickening_zero
        pointsSet_last isScheme_schemeStage isFinite_cover finitePresentation_cover
        surjective_cover diffOpen_pointsSet isFinite_cover_diffOpen
        etale_cover_diffOpen).schemeStage =
      schemeStage :=
  sorry

/-- The cover morphisms of a filtration built by `ofStages` are the supplied
covers. -/
@[simp]
theorem ofStages_cover {X : AlgebraicSpace S} (bound : ℕ)
    (closedStage : Fin (bound + 1) → ClosedSubspace X)
    (schemeStage : Fin bound → AlgebraicSpace S)
    (cover : ∀ i, schemeStage i ⟶ (closedStage i.castSucc).X)
    (diffOpen : ∀ i, OpenSubspace (closedStage i.castSucc).X)
    (stageIncl : ∀ i : Fin bound, (closedStage i.succ).X ⟶ (closedStage i.castSucc).X)
    (isClosedImmersion_stageIncl : ∀ i, IsClosedImmersion (stageIncl i))
    (stageIncl_ι :
      ∀ i : Fin bound, stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι)
    (antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet)
    (finitePresentation_closedStage : ∀ i, FinitePresentation (closedStage i).ι)
    (isThickening_zero : IsThickening (closedStage 0).ι)
    (pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅)
    (isScheme_schemeStage : ∀ i, IsScheme (schemeStage i))
    (isFinite_cover : ∀ i, IsFinite (cover i))
    (finitePresentation_cover : ∀ i, FinitePresentation (cover i))
    (surjective_cover : ∀ i, Surjective (cover i))
    (diffOpen_pointsSet :
      ∀ i, (diffOpen i).pointsSet = closedStratumOpenPoints closedStage i)
    (isFinite_cover_diffOpen :
      ∀ i, IsFinite (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf))
    (etale_cover_diffOpen :
      ∀ i, Etale (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf)) :
    (ofStages bound closedStage schemeStage cover diffOpen stageIncl
        isClosedImmersion_stageIncl stageIncl_ι
        antitone_pointsSet finitePresentation_closedStage isThickening_zero
        pointsSet_last isScheme_schemeStage isFinite_cover finitePresentation_cover
        surjective_cover diffOpen_pointsSet isFinite_cover_diffOpen
        etale_cover_diffOpen).cover =
      cover :=
  sorry

/-- The successive inclusions of a filtration built by `ofStages` are the supplied
inclusions. -/
@[simp]
theorem ofStages_stageIncl {X : AlgebraicSpace S} (bound : ℕ)
    (closedStage : Fin (bound + 1) → ClosedSubspace X)
    (schemeStage : Fin bound → AlgebraicSpace S)
    (cover : ∀ i, schemeStage i ⟶ (closedStage i.castSucc).X)
    (diffOpen : ∀ i, OpenSubspace (closedStage i.castSucc).X)
    (stageIncl : ∀ i : Fin bound, (closedStage i.succ).X ⟶ (closedStage i.castSucc).X)
    (isClosedImmersion_stageIncl : ∀ i, IsClosedImmersion (stageIncl i))
    (stageIncl_ι :
      ∀ i : Fin bound, stageIncl i ≫ (closedStage i.castSucc).ι = (closedStage i.succ).ι)
    (antitone_pointsSet : Antitone fun i ↦ (closedStage i).pointsSet)
    (finitePresentation_closedStage : ∀ i, FinitePresentation (closedStage i).ι)
    (isThickening_zero : IsThickening (closedStage 0).ι)
    (pointsSet_last : (closedStage (Fin.last bound)).pointsSet = ∅)
    (isScheme_schemeStage : ∀ i, IsScheme (schemeStage i))
    (isFinite_cover : ∀ i, IsFinite (cover i))
    (finitePresentation_cover : ∀ i, FinitePresentation (cover i))
    (surjective_cover : ∀ i, Surjective (cover i))
    (diffOpen_pointsSet :
      ∀ i, (diffOpen i).pointsSet = closedStratumOpenPoints closedStage i)
    (isFinite_cover_diffOpen :
      ∀ i, IsFinite (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf))
    (etale_cover_diffOpen :
      ∀ i, Etale (Open.inverseImageTo (cover i) (diffOpen i).ι
      (diffOpen i).isOpenImmersion.presheaf)) :
    (ofStages bound closedStage schemeStage cover diffOpen stageIncl
        isClosedImmersion_stageIncl stageIncl_ι
        antitone_pointsSet finitePresentation_closedStage isThickening_zero
        pointsSet_last isScheme_schemeStage isFinite_cover finitePresentation_cover
        surjective_cover diffOpen_pointsSet isFinite_cover_diffOpen
        etale_cover_diffOpen).stageIncl =
      stageIncl :=
  sorry

/-- The nested inclusions, finite-presentation, thickening, emptiness, scheme-cover,
and finite-étale-over-difference conditions of a finite closed scheme-cover
filtration. -/
theorem spec {X : AlgebraicSpace S} (F : FiniteClosedSchemeCoverFiltration X) :
    (∀ i, F.stageIncl i ≫ (F.closedStage i.castSucc).ι = (F.closedStage i.succ).ι) ∧
      (∀ i, IsClosedImmersion (F.stageIncl i)) ∧
      Antitone (fun i ↦ (F.closedStage i).pointsSet) ∧
      (∀ i, FinitePresentation (F.closedStage i).ι) ∧
      IsThickening (F.closedStage 0).ι ∧
      (F.closedStage (Fin.last F.bound)).pointsSet = ∅ ∧
      (∀ i, IsScheme (F.schemeStage i)) ∧
      (∀ i, IsFinite (F.cover i)) ∧
      (∀ i, FinitePresentation (F.cover i)) ∧
      (∀ i, Surjective (F.cover i)) ∧
      (∀ i, (F.diffOpen i).pointsSet = closedStratumOpenPoints F.closedStage i) ∧
      (∀ i, IsFinite (Open.inverseImageTo (F.cover i) (F.diffOpen i).ι
        (F.diffOpen i).isOpenImmersion.presheaf)) ∧
      ∀ i, Etale (Open.inverseImageTo (F.cover i) (F.diffOpen i).ι
        (F.diffOpen i).isOpenImmersion.presheaf) :=
  sorry

end FiniteClosedSchemeCoverFiltration

/-- Every quasi-compact, absolutely quasi-separated algebraic space admits a finite
closed filtration of finite presentation, beginning with a thickening and ending empty,
with surjective finite finitely presented scheme covers that are finite étale over
successive differences. -/
theorem exists_finiteClosedSchemeCoverFiltration {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    Nonempty (FiniteClosedSchemeCoverFiltration X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
