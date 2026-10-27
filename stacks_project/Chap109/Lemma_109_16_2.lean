/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Smooth.StructureMorphism
import StacksCheckRecall

/-!
# Smooth curves as a stack

The open substack `𝒞urves^{smooth} ⊂ 𝒞urves` has smooth structure morphism to
`Spec(Z)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsFiberedInGroupoids_smooth :
  ∀ (S : Scheme.{u}), Functor.IsFibered.InGroupoids ((smooth S).ι ⋙ p S))

/- Lemma 109.16.2: the morphism `𝒞urves^{smooth} ⟶ Spec(Z)` is smooth;
after base change, the smooth-curve stack over `S` is smooth over `S`. -/
@[stacks 0E1N] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_smooth :
  ∀ (S : Scheme.{u}), CohStack.Hom.Smooth
    (inclusionOf (smooth S) ≫ CohStack.toIdentitySlice (toGroupoids S)))

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
