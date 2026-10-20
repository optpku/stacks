module

public import ReasLib.CategoryTheory.Filtration.Complex.StageTower
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# The spectral sequence of a filtered cochain complex

The increasing diagram of stages indexed by negated integers gives a mapping-cone
spectral object. Its cohomology produces the spectral sequence starting at the first page.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.ExplicitSpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The increasing integer diagram whose value at `i` is the filtration stage `F^(-i)`. -/
def stageDiagram (K : FilteredComplex C) : ℤ ⥤ CochainComplex C ℤ :=
  ( { obj := fun i ↦ op (-i)
      map := fun f ↦ (homOfLE (neg_le_neg f.le)).op
      map_id := fun _ ↦ Subsingleton.elim _ _
      map_comp := fun _ _ ↦ Subsingleton.elim _ _ } : ℤ ⥤ ℤᵒᵖ) ⋙
    StageTower.diagram K

/-- The spectral object of cohomology groups of cones of filtration-stage inclusions. -/
def spectralObject (K : FilteredComplex C) : Abelian.SpectralObject C ℤ :=
  let T := (HomotopyCategory.spectralObjectMappingCone C).precomp (stageDiagram K)
  let H := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0
  { H := fun n ↦ T.ω₁ ⋙ HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n
    δ' := fun n₀ n₁ h ↦
      { app := fun D ↦ H.homologySequenceδ (T.ω₂.obj D) n₀ n₁ h
        naturality := fun D D' φ ↦
          H.homologySequenceδ_naturality _ _ (T.ω₂.map φ) n₀ n₁ h }
    exact₁' := fun n₀ n₁ h D ↦
      (H.homologySequence_exact₁ _ (T.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows
    exact₂' := fun n D ↦
      (H.homologySequence_exact₂ _ (T.ω₂_obj_distinguished D) n).exact_toComposableArrows
    exact₃' := fun n₀ n₁ h D ↦
      (H.homologySequence_exact₃ _ (T.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows }

/-- The integer index recipe for the first-page cohomological spectral sequence,
with total degree `p + q` and differential degree `(r, 1 - r)`. -/
def pageOneData :
    Abelian.SpectralObject.SpectralSequenceDataCore ℤ
      (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1 where
  deg pq := pq.1 + pq.2
  i₀ r pq hr := -pq.1 - r
  i₁ pq := -pq.1 - 1
  i₂ pq := -pq.1
  i₃ r pq hr := -pq.1 + r - 1
  le₀₁ r pq hr := by lia
  le₁₂ pq := by lia
  le₂₃ r pq hr := by lia
  hc := by rintro r pq _ rfl hr; dsimp; lia
  hc₀₂ := by rintro r pq _ rfl hr; dsimp; lia
  hc₁₃ := by rintro r pq _ rfl hr; dsimp; lia
  antitone_i₀ r r' pq hr hrr' := by lia
  monotone_i₃ r r' pq hr hrr' := by lia
  i₀_prev := by rintro r r' pq _ rfl hrr' hr; dsimp; lia +mbtc
  i₃_next := by rintro r r' pq _ rfl hrr' hr; dsimp; lia +mbtc

/-- Integer page shapes have both predecessors and successors, so there are no
boundary conditions for constructing their spectral sequence. -/
instance hasSpectralSequence (K : FilteredComplex C) :
    (spectralObject K).HasSpectralSequence pageOneData where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    exact False.elim (hpq _ rfl)
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    exact False.elim (hpq (pq - (r, 1 - r)) (by simp))

/-- The cohomological spectral sequence of a filtered cochain complex, starting at E1. -/
def sequence (K : FilteredComplex C) : CohomologicalSpectralSequence C 1 :=
  (spectralObject K).spectralSequence pageOneData

/-- The first page in bidegree `(p,q)` is isomorphic to degree `p+q` cohomology
of the `p`th graded-piece complex. -/
theorem pageOne_isomorphic (K : FilteredComplex C) (p q : ℤ) :
    IsIsomorphic (((sequence K).page 1 le_rfl).X (p, q))
      ((K.gradedPiece p).homology (p + q)) := sorry

end CategoryTheory.FilteredComplex.ExplicitSpectralSequence
