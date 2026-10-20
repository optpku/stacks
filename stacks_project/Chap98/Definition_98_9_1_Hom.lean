/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Hom
public import stacks_project.Chap98.Definition_98_9_1_AlgebraHom

/-! # Compatible stage maps of formal objects -/

@[expose] public section

universe u

variable {S : AlgebraicGeometry.Scheme.{u}}

variable [AlgebraicGeometry.IsLocallyNoetherian S] {X : AlgebraicGeometry.GroupoidsOver S}

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.Hom :
  AlgebraicGeometry.GroupoidsOver.FormalObject X →
    AlgebraicGeometry.GroupoidsOver.FormalObject X → Type u)
