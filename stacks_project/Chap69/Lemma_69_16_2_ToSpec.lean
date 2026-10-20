/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Equivalence

/-! # Compatibility view of the canonical morphism to the spectrum of global sections -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

#check (AlgebraicGeometry.AlgebraicSpace.toSpecGamma :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), X ⟶ specGamma X)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.toScheme :
  ∀ {S : Scheme.{u}} (U : Over S), (ofOver U).Modules ⥤ U.left.Modules)
