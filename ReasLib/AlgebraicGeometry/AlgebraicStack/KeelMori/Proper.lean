/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.KeelMori
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Properness of Keel–Mori moduli spaces

If an algebraic stack of finite inertia maps properly to a locally Noetherian
algebraic space, then a uniform categorical moduli space induces a proper
morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- If an algebraic stack with finite inertia maps properly to a locally
Noetherian algebraic space, the induced morphism from any uniform categorical
moduli space is proper. The induced morphism is specified by an invertible
comparison 2-cell identifying its composite with the original morphism. -/
@[stacks 0DUZ]
theorem proper_of_isUniformCategoricalModuliSpace
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y M : AlgebraicSpace S} [IsFinite (forget.{u + 1, u, u, u + 1} X)]
    [AlgebraicSpace.IsLocallyNoetherian Y] (p : X ⟶ Y.toGroupoids)
    [Proper p] (f : X ⟶ M.toGroupoids)
    [IsUniformCategoricalModuliSpace f] (q : M ⟶ Y)
    (α : f ≫ AlgebraicSpace.toGroupoids.map q ≅ p) :
    AlgebraicSpace.Proper q :=
  sorry

end AlgebraicGeometry.AlgebraicStack
