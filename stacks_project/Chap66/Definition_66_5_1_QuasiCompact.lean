/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Quasi-compact algebraic spaces

An algebraic space is quasi-compact when it admits a representable étale locally-surjective
atlas from a quasi-compact scheme.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
