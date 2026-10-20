/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Counit.Abelian
public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Tower.Mono

/-!
# Skeleton towers in abelian categories

In an abelian category, skeleton counits are monomorphisms.  Combined with the category-generic
instances from `Skeleton.Tower.Mono`, this makes every transition in the canonical skeleton tower
monomorphic without a second abelian-specific proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Skeleton

variable {A : Type u} [Category.{v} A] [Abelian A]

variable (V : SimplicialObject A)

end CategoryTheory.SimplicialObject.Skeleton
