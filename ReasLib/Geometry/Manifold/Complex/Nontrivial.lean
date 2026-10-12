/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

@[expose] public section

/-!
# Nontrivial complex charted spaces

A complex chart around a point forces its source to contain more than one point.
-/

open scoped Manifold Topology

universe u

/-- A complex chart around any point contains two distinct points of its source. -/
theorem complexChartedSpace_nontrivial
    (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) : Nontrivial X := by
  let e := chartAt ℂ x
  let p : ℂ := e x
  have htarget : e.target ∈ 𝓝 p := by
    simpa [e, p] using chart_target_mem_nhds (H := ℂ) x
  have htarget' : e.target ∈ 𝓝[≠] p := mem_nhdsWithin_of_mem_nhds htarget
  have hpunct : ({p}ᶜ : Set ℂ) ∈ 𝓝[≠] p := self_mem_nhdsWithin
  obtain ⟨y, hy_target, hy_ne⟩ :=
    (Filter.NeBot.nonempty_of_mem (inferInstance : Filter.NeBot (𝓝[≠] p))
      (Filter.inter_mem htarget' hpunct))
  refine nontrivial_iff.2 ⟨e.symm y, x, ?_⟩
  intro hsymm
  apply hy_ne
  have hy_eq : e (e.symm y) = y := e.right_inv hy_target
  calc
    y = e (e.symm y) := hy_eq.symm
    _ = e x := by rw [hsymm]
    _ = p := rfl
