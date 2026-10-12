/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import stacks_project.Chap109.Lemma_109_22_7_Substack

/-!
# Smoothness of the moduli stacks of stable curves

The structure morphisms `ℳ̄ ⟶ Spec(Z)` and, for `2 ≤ g`, `ℳ̄_g ⟶ Spec(Z)`
are smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.22.6 (1): the structure morphism `ℳ̄ ⟶ Spec(Z)` is smooth. -/
@[stacks 0E79]
instance instSmooth_stable (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (stable S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- Lemma 109.22.6 (2): for `2 ≤ g`, the structure morphism `ℳ̄_g ⟶ Spec(Z)`
is smooth. -/
@[stacks 0E79]
instance instSmooth_stableOfGenus (g : ℕ) (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (stableOfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
