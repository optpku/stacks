/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Specializations
import StacksCheckRecall

/-!
# Definition 95.18.2

The degree `d` finite Hilbert stack `H_d(X/Y)` of a 1-morphism of stacks in
groupoids over `(Sch/S)_fppf`, together with the specializations `H_d(X)` and
`H_d`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

/- Definition 95.18.2 (1): the degree `d` finite Hilbert stack `H_d(X/Y)` of a
1-morphism `F : X ⟶ Y` of stacks in groupoids over `(Sch/S)_fppf`. -/
@[stacks 05WC]
#check (AlgebraicGeometry.FiniteHilbertStack.stack :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p],
    (X ⟶ Y) → ℕ → StackOver.Groupoids (Scheme.fppfTopology.over S))

/- Definition 95.18.2 (2): if `Y = S`, write `H_d(X)` for `H_d(X/S)`. -/
@[stacks 05WC]
#check (AlgebraicGeometry.FiniteHilbertStack.ofStack :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p],
    ℕ → StackOver.Groupoids (Scheme.fppfTopology.over S))

/- Definition 95.18.2 (3): if `X = Y = S`, denote the stack by `H_d`. -/
@[stacks 05WC]
#check (AlgebraicGeometry.FiniteHilbertStack.ofScheme :
  ∀ (S : Scheme.{u}), ℕ → StackOver.Groupoids (Scheme.fppfTopology.over S))

end AlgebraicGeometry.FiniteHilbertStack
