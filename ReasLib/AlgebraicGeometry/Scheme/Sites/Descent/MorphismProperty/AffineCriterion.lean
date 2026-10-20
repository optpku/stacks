/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.MorphismProperty.SatisfiesDescent

open AlgebraicGeometry

/-- A scheme morphism property stable under base change and finite coproducts satisfies descent
for a non-Zariski topology if descent data for affine singleton covers are effective. -/
theorem of_affine
    (P : MorphismProperty Scheme.{u}) (τ : DescentTopology) (hτ : τ ≠ .zariski)
    [P.IsStableUnderBaseChange] [P.IsStableUnderFiniteCoproducts]
    (h_effective : ∀ {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
      (p : X ⟶ S) (hp : Presieve.singleton p ∈ τ.precoverage S)
      (D : Scheme.DescentData (fun _ : PUnit ↦ X) (fun _ ↦ p)),
        P (D.obj PUnit.unit).hom → D.IsEffective) :
    P.SatisfiesDescent τ := sorry

end CategoryTheory.MorphismProperty.SatisfiesDescent
