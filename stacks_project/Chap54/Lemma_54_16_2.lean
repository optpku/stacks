/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Contraction

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 54.16.2: any two contractions of an exceptional curve of the first kind on a
Noetherian scheme are related by a unique isomorphism commuting with the contraction maps. -/
@[stacks 0C5K] #check
  (AlgebraicGeometry.IsContraction.existsUnique_iso :
    ∀ {X Y₁ Y₂ : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
      {E : X.IdealSheafData} [AlgebraicGeometry.IsExceptionalCurveFirstKind E]
      {b₁ : X ⟶ Y₁} {y₁ : closedPoints Y₁}
      (h₁ : AlgebraicGeometry.IsContraction E b₁ y₁)
      {b₂ : X ⟶ Y₂} {y₂ : closedPoints Y₂}
      (h₂ : AlgebraicGeometry.IsContraction E b₂ y₂),
      ∃! e : Y₁ ≅ Y₂, b₁ ≫ e.hom = b₂)
