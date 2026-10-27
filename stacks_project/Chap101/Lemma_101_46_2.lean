/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Normalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.46.2 (1). The absolute normalization morphism of an algebraic stack
satisfying the finite-components condition is integral. -/
@[stacks 0GMJ] #check
  (AlgebraicGeometry.AlgebraicStack.instIsIntegralHom_normalizationTo :
    {S : Scheme.{u}} → (X : GroupoidsOver S) →
      [AlgebraicStack X] → [HasFiniteIrreducibleComponentsOnCompactOpens X] →
      IsIntegralHom (normalizationTo X))

/- Lemma 101.46.2 (2). Absolute normalization pulls back to the normalization of
every smooth scheme over the stack, compatibly with the projection to that scheme. -/
@[stacks 0GMJ] #check
  (AlgebraicGeometry.AlgebraicStack.exists_pullbackEquivalence_of_smooth :
    {S : Scheme.{u}} → (X : GroupoidsOver S) →
      [AlgebraicStack X] → [HasFiniteIrreducibleComponentsOnCompactOpens X] →
      (U : Over S) → (p : GroupoidsOver.slice U ⟶ X) → [Groupoids.Hom.Smooth p] →
      ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} (normalizationTo X) p ≌
          GroupoidsOver.slice (smoothSliceOverNormalization U p),
        Nonempty
          (e.hom ≫ sliceNormalizationHom U p ≅
            TwoFibreProduct.snd.{u + 1, u, u + 1, u} (normalizationTo X) p))
