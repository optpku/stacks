/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CompletelyDecomposed
import StacksCheckRecall

open CategoryTheory

universe u v

/- Definition 37.78.1 (1): a scheme morphism is completely decomposed when it
has a lift of every target residue-field point. -/
@[stacks 0GTI] #check (AlgebraicGeometry.Scheme.Hom.CompletelyDecomposed :
  {X T : AlgebraicGeometry.Scheme.{u}} → (X ⟶ T) → Prop)

/- Definition 37.78.1 (2): a family of scheme morphisms with fixed target is
completely decomposed when its family property holds pointwise. -/
@[stacks 0GTI] #check (AlgebraicGeometry.CompletelyDecomposedFamily :
  {I : Type v} → {T : AlgebraicGeometry.Scheme.{u}} →
    (X : I → AlgebraicGeometry.Scheme.{u}) → (∀ i, X i ⟶ T) → Prop)
