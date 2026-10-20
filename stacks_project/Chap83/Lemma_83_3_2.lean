/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap83.Lemma_83_3_2_Invariant
public import stacks_project.Chap83.Lemma_83_3_2_QuotientSheaf
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 83.3.2: a morphism φ : U ⟶ X of algebraic spaces over B is R-invariant
if and only if it factors as U ⟶ U/R ⟶ X in fppf sheaves. -/
@[stacks 048F] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isInvariantHom_iff_factors :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {B : AlgebraicGeometry.AlgebraicSpace S}
      {U X : CategoryTheory.Over B}
      (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
      (φ : U ⟶ X),
      P.IsInvariantHom φ ↔
        ∃ ψ : P.quotientSheaf ⟶
            AlgebraicGeometry.AlgebraicSpace.toSheaf.obj X.left,
          P.quotientMap ≫ ψ = AlgebraicGeometry.AlgebraicSpace.toSheaf.map φ.left)
