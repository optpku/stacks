/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_33_1_Affine
public import stacks_project.Chap109.Lemma_109_22_7_Substack

/-!
# Quasi-compactness of the stack of stable curves of genus `g`

For `2 ≤ g`, the algebraic stack `ℳ̄_g` of stable genus-`g` curves over
`specZ` admits a surjective smooth atlas from a quasi-compact scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.25.2: for `2 ≤ g`, the algebraic stack `ℳ̄_g` of stable
genus-`g` curves is quasi-compact, as witnessed by a surjective smooth atlas
from a quasi-compact scheme over `specZ`. -/
@[stacks 0E9B]
theorem isQuasiCompact_stableOfGenus (g : ℕ) (hg : 2 ≤ g) :
    ∃ (U : Over specZ) (p : Classifying.slice U ⟶ ofObjectProperty (stableOfGenus g specZ)),
      Classifying.Smooth p ∧ Classifying.Surjective p ∧ CompactSpace U.left :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
