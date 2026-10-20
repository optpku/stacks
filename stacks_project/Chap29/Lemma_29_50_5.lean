/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.DenseOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 29.50.5 (1): a birational morphism between schemes with finitely many irreducible
components restricts to an isomorphism between dense opens if it is locally of finite type with
reduced target, or if it is locally of finite presentation. -/
@[stacks 0BAC] #check
  (AlgebraicGeometry.IsBirational.exists_dense_opens_isIso_resLE :
    ∀ {X Y : Scheme.{u}}
      [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
      (f : X ⟶ Y) [IsBirational f],
      ((LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) →
        ∃ (U : X.Opens) (V : Y.Opens),
          Dense (U : Set X) ∧ Dense (V : Set Y) ∧
            ∃ hUV : U ≤ f ⁻¹ᵁ V, IsIso (f.resLE V U hUV))

/- Lemma 29.50.5 (2): if the source and target are irreducible and the morphism is compatible
with their maps to `S`, then the schemes are birational over `S`. -/
@[stacks 0BAC] #check
  (AlgebraicGeometry.IsBirational.birationalOver_of_irreducible :
    ∀ {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
      [IrreducibleSpace X] [IrreducibleSpace Y]
      (f : X ⟶ Y) [IsBirational f],
      f ≫ (Y ↘ S) = (X ↘ S) →
        ((LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) →
          AlgebraicGeometry.Scheme.BirationalOver (X ↘ S) (Y ↘ S))
