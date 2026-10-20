/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.20.10: a scheme morphism is quasi-finite if and only if it is locally of finite
type, quasi-compact, and has finite point-set fibers over every target point. -/
@[stacks 02NH] #check
  (AlgebraicGeometry.Scheme.Hom.quasiFinite_iff_locallyOfFiniteType_and_quasiCompact_and_finiteFibers :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.Scheme.Hom.QuasiFinite f ↔
        AlgebraicGeometry.LocallyOfFiniteType f ∧ AlgebraicGeometry.QuasiCompact f ∧
          ∀ s : S, Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S)))
