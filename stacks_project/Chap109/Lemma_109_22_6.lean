/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Stable.Smooth
import StacksCheckRecall

/-!
# Smoothness of the moduli stacks of stable curves

The structure morphisms `ℳ̄ ⟶ Spec(Z)` and, for `2 ≤ g`, `ℳ̄_g ⟶ Spec(Z)`
are smooth. The checks below express their base changes over an arbitrary
scheme `S`, retaining the source-defined genus range `2 ≤ g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/- Lemma 109.22.6: the structure morphisms of the stable moduli stack and its
genus-`g` loci, for `2 ≤ g`, are smooth, also after base change to a scheme. -/
@[stacks 0E79] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_stable :
    ∀ (S : Scheme.{u}),
    CohStack.Hom.Smooth
      (inclusionOf (stable S) ≫ CohStack.toIdentitySlice (toGroupoids S)))

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_stableOfGenus :
    ∀ (g : ℕ) (S : Scheme.{u}) [Fact (2 ≤ g)],
    CohStack.Hom.Smooth
      (inclusionOf (stableOfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)))

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
