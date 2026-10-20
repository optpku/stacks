/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Immersion

/-!
# An immersion in infinite affine space

This module constructs an explicit immersion into the spectrum of a polynomial ring in
countably many variables which does not factor as an open immersion followed by a closed
immersion.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.InfiniteAffineCounterexample

variable (k : Type u) [Field k]

/-- The localization of the infinite polynomial ring at one coordinate. -/
abbrev ChartRing (n : ℕ) :=
  Localization.Away (PuncturedAffineSpace.coordinate ℕ k n)

/-- The canonical map from the infinite polynomial ring to a coordinate chart ring. -/
def localizationMap (n : ℕ) :
    PuncturedAffineSpace.coordinateRing ℕ k →+* ChartRing k n :=
  algebraMap (PuncturedAffineSpace.coordinateRing ℕ k) (ChartRing k n)

/-- For the zero-based chart index `n`, the explicit ideal generators are the `(n + 1)`-st
powers of lower coordinates, the distinguished relation `xₙ - 1`, and all higher
coordinates. -/
def chartIdealGenerators (n : ℕ) : Set (ChartRing k n) :=
  {f |
    (∃ i : ℕ, i < n ∧
      f = localizationMap k n
        ((PuncturedAffineSpace.coordinate ℕ k i) ^ (n + 1))) ∨
    f = localizationMap k n (PuncturedAffineSpace.coordinate ℕ k n - 1) ∨
    ∃ m : ℕ, n < m ∧
      f = localizationMap k n (PuncturedAffineSpace.coordinate ℕ k m)}

/-- The ideal generated on a coordinate chart by the lower coordinate powers, the relation
`xₙ - 1`, and all higher coordinates. -/
def chartIdeal (n : ℕ) : Ideal (ChartRing k n) :=
  Ideal.span (chartIdealGenerators k n)

/-- Away from the chart of index `n`, the ideal on that chart becomes the unit ideal. -/
theorem map_chartIdeal_overlap {n m : ℕ} (h : m ≠ n) :
    (chartIdeal k n).map
      (algebraMap (ChartRing k n)
        (Localization.Away
          (localizationMap k n (PuncturedAffineSpace.coordinate ℕ k m)))) = ⊤ := sorry

/-- Every coordinate-chart ideal is nonzero. -/
theorem chartIdeal_ne_bot (n : ℕ) :
    chartIdeal k n ≠ ⊥ := sorry

/-- A polynomial belonging to every coordinate-chart ideal after localization is zero. -/
theorem only_zero_mem_all_chartIdeals
    (f : PuncturedAffineSpace.coordinateRing ℕ k)
    (hf : ∀ n : ℕ, localizationMap k n f ∈ chartIdeal k n) :
    f = 0 := sorry

/-- The ideal sheaf on the punctured spectrum obtained from all closed coordinate-chart
subschemes. -/
def idealSheaf :
    ((PuncturedAffineSpace.coordinatePuncturedOpen ℕ k).toScheme).IdealSheafData :=
  let chartIdealSheaf : (n : ℕ) →
      (Spec (CommRingCat.of (ChartRing k n))).IdealSheafData :=
    fun n ↦ Scheme.IdealSheafData.ofIdealTop
      ((chartIdeal k n).map
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k n))).inv.hom)
  let chartMap : (n : ℕ) →
      (Spec (CommRingCat.of (ChartRing k n)) ⟶
        (PuncturedAffineSpace.coordinatePuncturedOpen ℕ k).toScheme) :=
    fun n ↦
      IsOpenImmersion.lift (PuncturedAffineSpace.coordinatePuncturedOpen ℕ k).ι
        (Spec.map (CommRingCat.ofHom
          (algebraMap (PuncturedAffineSpace.coordinateRing ℕ k) (ChartRing k n)))) (by
          rw [← Scheme.Hom.coe_opensRange,
            Scheme.Hom.opensRange_localizationAway
              (R := CommRingCat.of (PuncturedAffineSpace.coordinateRing ℕ k))
                (PuncturedAffineSpace.coordinate ℕ k n),
            Scheme.Opens.range_ι]
          exact le_iSup (fun m : ℕ ↦
            (PrimeSpectrum.basicOpen (PuncturedAffineSpace.coordinate ℕ k m) :
              TopologicalSpace.Opens
                (PrimeSpectrum (PuncturedAffineSpace.coordinateRing ℕ k)))) n)
  (Limits.Sigma.desc (fun n ↦
    (chartIdealSheaf n).subschemeι ≫ chartMap n)).ker

/-- Pulling the glued ideal sheaf back to a coordinate chart recovers its explicit chart
ideal. -/
theorem comap_idealSheaf_chart (n : ℕ) :
    (idealSheaf k).comap
      (IsOpenImmersion.lift (PuncturedAffineSpace.coordinatePuncturedOpen ℕ k).ι
        (Spec.map (CommRingCat.ofHom
          (algebraMap (PuncturedAffineSpace.coordinateRing ℕ k) (ChartRing k n)))) (by
          rw [← Scheme.Hom.coe_opensRange,
            Scheme.Hom.opensRange_localizationAway
              (R := CommRingCat.of (PuncturedAffineSpace.coordinateRing ℕ k))
                (PuncturedAffineSpace.coordinate ℕ k n),
            Scheme.Opens.range_ι]
          exact PuncturedAffineSpace.basicOpen_coordinate_le_coordinatePuncturedOpen ℕ k n)) =
      Scheme.IdealSheafData.ofIdealTop
        ((chartIdeal k n).map
          (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k n))).inv.hom) := sorry

/-- The closed subscheme of the punctured spectrum defined by the glued ideal sheaf. -/
def closedSubscheme : Scheme.{u} :=
  (idealSheaf k).subscheme

/-- The closed subscheme defined by the glued ideal sheaf on punctured countable affine space
does not extend to a closed subscheme of the ambient affine scheme. -/
theorem closedSubscheme_not_extends :
    ¬ ∃ (J : (PuncturedAffineSpace.coordinateSpectrum ℕ k).IdealSheafData),
      J.comap (PuncturedAffineSpace.coordinatePuncturedOpen ℕ k).ι = idealSheaf k := sorry

/-- The morphism from the closed subscheme into the ambient infinite affine scheme. -/
def immersion :
    closedSubscheme k ⟶ PuncturedAffineSpace.coordinateSpectrum ℕ k :=
  (idealSheaf k).subschemeι ≫
    (PuncturedAffineSpace.coordinatePuncturedOpen ℕ k).ι

/-- The canonical morphism from the glued closed subscheme to the ambient scheme is an
immersion. -/
instance immersion_isImmersion : IsImmersion (immersion k) := by
  change IsImmersion ((idealSheaf k).subschemeι ≫
    (PuncturedAffineSpace.coordinatePuncturedOpen ℕ k).ι)
  infer_instance

/-- The explicit immersion does not factor as an open immersion followed by a closed
immersion. -/
theorem not_isOpenThenClosed :
    ¬ IsOpenThenClosed (immersion k) := sorry

/-- The explicit morphism is an immersion which does not factor as an open immersion followed
by a closed immersion. -/
theorem immersion_spec :
    IsImmersion (immersion k) ∧ ¬ IsOpenThenClosed (immersion k) :=
  ⟨inferInstance, not_isOpenThenClosed k⟩

end AlgebraicGeometry.InfiniteAffineCounterexample
