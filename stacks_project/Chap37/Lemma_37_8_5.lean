/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale.Restriction
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.8.5: A formally étale scheme morphism remains formally étale after restriction
to compatible open subschemes of its source and target. -/
@[stacks 02HK] #check
  (@AlgebraicGeometry.FormallyEtale.resLE :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
      (e : U ≤ f ⁻¹ᵁ V) [AlgebraicGeometry.FormallyEtale f],
      AlgebraicGeometry.FormallyEtale (f.resLE V U e))
