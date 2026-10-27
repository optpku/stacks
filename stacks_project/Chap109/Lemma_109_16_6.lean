/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SmoothH0.StructureMorphism
import StacksCheckRecall

/-!
# Smoothness of the moduli stacks of smooth proper curves

The structure morphisms `ℳ ⟶ Spec(Z)` and `ℳ_g ⟶ Spec(Z)` are smooth,
where `ℳ` is the moduli stack of smooth proper curves and `ℳ_g` is the
open-and-closed genus-`g` piece. The general statements below concern their
base changes over an arbitrary scheme `S`; specializing to `S = Spec(Z)`
gives the stated structure morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/- Lemma 109.16.6 (1): the structure morphism of `ℳ` is smooth,
as is its base change over any scheme `S`. -/
@[stacks 0E84] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_smoothH0 :
    ∀ (S : Scheme.{u}), CohStack.Hom.Smooth
      (inclusionOf (smoothH0 S) ≫ CohStack.toIdentitySlice (toGroupoids S)))

/- Lemma 109.16.6 (2): the structure morphism of `ℳ_g` is smooth,
as is its base change over any scheme `S`. -/
@[stacks 0E84] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_smoothH0OfGenus :
    ∀ (g : ℕ) (S : Scheme.{u}), CohStack.Hom.Smooth
      (inclusionOf (smoothH0OfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)))

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
