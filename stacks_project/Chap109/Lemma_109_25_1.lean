/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_33_1_Affine
public import stacks_project.Chap109.Lemma_109_22_7_Substack
public import stacks_project.Chap109.Lemma_109_25_1_Separated

/-!
# Separatedness of the moduli stack of stable curves of genus `g`

For `2 ≤ g`, the algebraic stack `ℳ̄_g` of stable genus-`g` curves is
separated, meaning that the structure morphism `ℳ̄_g ⟶ Spec(Z)` is
separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.25.1: for `2 ≤ g`, the algebraic stack `ℳ̄_g` of stable
genus-`g` curves is separated, i.e. the structure morphism
`ℳ̄_g ⟶ Spec(Z)` is separated. -/
@[stacks 0E9A]
instance instSeparated_stableOfGenus (g : ℕ) [Nat.AtLeastTwo g] :
    CohStack.Hom.Separated
      (CohStack.toIdentitySlice (ofObjectProperty (stableOfGenus g specZ))) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
