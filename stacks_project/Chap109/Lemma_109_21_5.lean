/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Semistable.Smooth
import StacksCheckRecall

/-!
# Smoothness of the moduli stacks of semistable curves

The structure morphisms `𝒞urves^{semistable} ⟶ Spec(Z)` and
`𝒞urves^{semistable}_g ⟶ Spec(Z)` are smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsFiberedInGroupoids_semistable :
  ∀ (S : Scheme.{u}), Functor.IsFibered.InGroupoids ((semistable S).ι ⋙ p S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsFiberedInGroupoids_semistableOfGenus :
  ∀ (g : ℕ) (S : Scheme.{u}),
    Functor.IsFibered.InGroupoids ((semistableOfGenus g S).ι ⋙ p S))

/- Lemma 109.21.5 (1): the structure morphism `𝒞urves^{semistable} ⟶ Spec(Z)`
is smooth. -/
@[stacks 0E72]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_semistable :
  ∀ (S : Scheme.{u}),
    CohStack.Hom.Smooth
      (inclusionOf (semistable S) ≫ CohStack.toIdentitySlice (toGroupoids S)))

/- Lemma 109.21.5 (2): the structure morphism
`𝒞urves^{semistable}_g ⟶ Spec(Z)` is smooth. -/
@[stacks 0E72]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_semistableOfGenus :
  ∀ (g : ℕ) (S : Scheme.{u}),
    CohStack.Hom.Smooth
      (inclusionOf (semistableOfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)))

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
