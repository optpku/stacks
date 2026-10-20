/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.OverField
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open DerivedCategory.TStructure

universe u

/- Example 76.52.2 (1): over a field, an object of `D(𝒪_X)` on an algebraic space of
finite presentation over `k` is `k`-perfect if and only if it is bounded and
pseudo-coherent. -/
@[stacks 0DKP] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.OverField.isPerfectRelativeTo_iff_bounded_and_pseudoCoherent :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (.of k)))
      [FinitePresentation (SchemeRealization.toBase X)] (E : ModuleDerived X),
      IsPerfectRelativeTo (SchemeRealization.toBase X) E ↔
        (t.bounded : ObjectProperty (ModuleDerived X)) E ∧ IsPseudoCoherent X E)

/- Example 76.52.2 (2): over a field, an object of `D(𝒪_X)` on an algebraic space of
finite presentation over `k` is `k`-perfect if and only if it lies in
`t.bounded ⊓ cohomologyIn (SheafOfModules.isCoherent (structureSheaf X))`. This is a
relative condition and does not assert perfectness on every fibre. -/
@[stacks 0DKP] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.OverField.isPerfectRelativeTo_iff_bounded_and_coherentCohomology :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (.of k)))
      [FinitePresentation (SchemeRealization.toBase X)] (E : ModuleDerived X),
      IsPerfectRelativeTo (SchemeRealization.toBase X) E ↔
        (t.bounded : ObjectProperty (ModuleDerived X)) E ∧
          DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent (structureSheaf X)) E)
