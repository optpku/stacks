/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap109.Lemma_109_22_8_Inclusion

/-!
# Lemma 109.22.8

For `g ≥ 2`, the inclusion `|ℳ_g| ⊂ |ℳ̄_g|` is that of an open dense
subset of the canonical topology on points of the moduli stack of stable
genus-`g` curves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- Lemma 109.22.8 (1): Let `g ≥ 2`. The inclusion `|ℳ_g| ⊂ |ℳ̄_g|` is
that of an open subset. -/
@[stacks 0E87]
theorem isOpen_smoothH0OfGenusPointsSet (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    IsOpen (Set.range (CohStack.Points.map (inclusionSmoothStableOfGenus g hg S))) :=
  sorry

/-- Lemma 109.22.8 (2): Let `g ≥ 2`. The inclusion `|ℳ_g| ⊂ |ℳ̄_g|` is
that of a dense subset. -/
@[stacks 0E87]
theorem dense_smoothH0OfGenusPointsSet (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    Dense (Set.range (CohStack.Points.map (inclusionSmoothStableOfGenus g hg S))) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
