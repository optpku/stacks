/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 29.49.7 (1): noncontainment of irreducible closed subsets of an integral separated
scheme is reflected by noncontainment of their generic-point stalk images in the function field. -/
@[stacks 02NF] #check
  (AlgebraicGeometry.Scheme.genericPointStalkRange_not_subset_of_not_subset :
    ∀ {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated] (Z₁ Z₂ : IrreducibleCloseds X),
      (¬ (Z₁ : Set X) ⊆ Z₂) →
        ¬ X.genericPointStalkInFunctionField Z₁ ≤ X.genericPointStalkInFunctionField Z₂)

/- Lemma 29.49.7 (2): if a closed point lies outside an irreducible closed subset, then some
function regular near that point has germ outside the subset's generic-point stalk image. -/
@[stacks 02NF] #check
  (AlgebraicGeometry.Scheme.exists_regularFunction_near_closedPoint_not_mem_genericPointStalk :
    ∀ {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated] (Z₂ : IrreducibleCloseds X) (x : X),
      IsClosed ({x} : Set X) → x ∉ (Z₂ : Set X) →
        ∃ (U : X.Opens) (hxU : x ∈ U) (f : Γ(X, U)),
          algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hxU f) ∉
            X.genericPointStalkInFunctionField Z₂)
