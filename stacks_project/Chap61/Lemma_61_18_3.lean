/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ProEtale.Lifting
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Scheme

universe u v

@[expose] public section

/- Lemma 61.18.3: a geometric point of a scheme lifts through some member of
any indexed pro-étale covering family, with the same source field. -/
@[stacks 0F6C] #check (AlgebraicGeometry.Scheme.GeometricPoint.exists_lift_of_proetaleCovering :
  ∀ {S : Scheme.{u}} (s : AlgebraicGeometry.Scheme.GeometricPoint S)
    {ι : Type v} (family : ι → Over S), Scheme.Proetale.IsCovering family →
      ∃ (i : ι) (s_i : Spec (.of s.K) ⟶ (family i).left),
        s_i ≫ (family i).hom = s.hom)
