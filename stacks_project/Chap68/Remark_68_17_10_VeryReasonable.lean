/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.VeryReasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.VeryReasonable

/-!
# Very reasonable algebraic spaces and morphisms
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (IsVeryReasonable : {S : Scheme.{u}} → AlgebraicSpace S → Prop)

#check (VeryReasonable : {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)

end AlgebraicGeometry.AlgebraicSpace
