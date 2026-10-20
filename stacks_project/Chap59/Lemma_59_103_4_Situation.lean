/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.EtaleCohomology
public import stacks_project.Chap59.Lemma_59_103_4_TorsionPullback

@[expose] public section

universe u

#check (AlgebraicGeometry.Scheme.HComparison.etale_le_h.{u} :
  AlgebraicGeometry.Scheme.etaleTopology.{u} ≤
    AlgebraicGeometry.Scheme.hPrecoverage.toGrothendieck)

end
