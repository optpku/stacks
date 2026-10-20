/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.IrreducibleComponent.Multiplicity
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.3.3: if `f1 : U1 ⟶ X` and `f2 : U2 ⟶ X` are smooth morphisms from
schemes to a locally Noetherian algebraic stack, `T1'` and `T2'` are irreducible
components of `|U1|` and `|U2|` whose image-closures are the same irreducible
component `T` of `|X|`, then `U1.left.irreducibleComponentMultiplicity T1'` equals
`U2.left.irreducibleComponentMultiplicity T2'`.

Closure equality implies the image-containment condition stored in
`ComponentChart`; conversely, `ComponentChart.closure_image_eq` gives closure
equality under the retained smoothness, local Noetherianity, and canonical
point-topology hypotheses. -/
@[stacks 0DR7]
#check (AlgebraicGeometry.AlgebraicStack.irreducibleComponentMultiplicity_independent :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    {T : @irreducibleComponents (Points X) τ} (c₁ c₂ : ComponentChart T),
    c₁.multiplicity = c₂.multiplicity)

end AlgebraicGeometry.AlgebraicStack
