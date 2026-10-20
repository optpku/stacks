/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Reanchor
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition

/-!
# The canonical operational Chern-class theory

The Chern classes `c_i(E) ∈ A^i(X)` of a finite locally free module, glued from
the fixed-rank classes on the clopen rank loci (Stacks, Remark 0ESW), form a
base-wide Chern-class theory.  Following the source, the classes are only
defined for finite locally free modules; on any other module the theory uses the
zero bivariant class, and every field which is not trivially true for zero
assumes finite local freeness.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass

variable {S : Scheme.{u}} (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]

/-- The base-wide Chern classes: `c_i(E)` from the rank decomposition when `E` is
finite locally free, and the zero class otherwise. -/
def canonicalBaseComponent (Y : Over S) [LocallyOfFiniteType Y.hom]
    (E : Y.left.Modules) (i : ℕ) : BivariantClass δ (𝟙 Y) (i : ℤ) := by
  classical
  exact if hE : E.IsFiniteLocallyFree then @chernClass S Y.left _ δ _ Y.hom _ E hE i
    else BivariantClass.pointwiseZero δ (𝟙 Y) (i : ℤ)

/-- On a finite locally free module the canonical base component is its Chern class. -/
theorem canonicalBaseComponent_of_isFiniteLocallyFree (Y : Over S)
    [LocallyOfFiniteType Y.hom] (E : Y.left.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    canonicalBaseComponent δ Y E i = chernClass δ Y.hom E i := sorry

/-- Off finite locally free modules the canonical base component is zero. -/
theorem canonicalBaseComponent_of_not_isFiniteLocallyFree (Y : Over S)
    [LocallyOfFiniteType Y.hom] (E : Y.left.Modules) (hE : ¬ E.IsFiniteLocallyFree)
    (i : ℕ) :
    canonicalBaseComponent δ Y E i = BivariantClass.pointwiseZero δ (𝟙 Y) (i : ℤ) := sorry

/-- The canonical Chern-class theory, whose classes are the Chern classes of
Stacks, Remark 0ESW.  Its axioms are the source results on pullback, first Chern
classes of invertible modules, normalization, vanishing above the rank,
centrality (02UA), Whitney sums, additivity of `c_1` on tensor products
(0FA6 in rank one), and the splitting principle (02UL). -/
def Theory.canonical {X : Scheme.{u}} (p : X ⟶ S) [LocallyOfFiniteType p] :
    Theory δ p where
  baseComponent := canonicalBaseComponent δ
  component_pullback := sorry
  component_one_cap := sorry
  component_zero := sorry
  component_iso := sorry
  component_eq_zero_of_rank_lt := sorry
  component_mem_center := sorry
  component_biprod := sorry
  component_one_tensor := sorry
  splitting_principle := sorry

/-- The base-wide classes of the canonical theory are `canonicalBaseComponent`. -/
theorem Theory.canonical_baseComponent {X : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFiniteType p] (Y : Over S) [LocallyOfFiniteType Y.hom]
    (E : Y.left.Modules) (i : ℕ) :
    (Theory.canonical δ p).baseComponent Y E i = canonicalBaseComponent δ Y E i := sorry

/-- The components of the canonical theory are the Chern classes `c_i(E)` assembled
from the rank decomposition. -/
theorem Theory.canonical_component {X : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFiniteType p] (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    (Theory.canonical δ p).component E i = chernClass δ p E i := sorry

/-- Reanchoring the canonical theory gives the canonical theory. -/
theorem Theory.canonical_reanchor {X : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFiniteType p] (Y : Over S) [LocallyOfFiniteType Y.hom] :
    (Theory.canonical δ p).reanchor Y = Theory.canonical δ Y.hom := sorry

end AlgebraicGeometry.ChernClass
