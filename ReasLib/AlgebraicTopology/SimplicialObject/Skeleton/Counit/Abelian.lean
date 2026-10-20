/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Counit
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Skeleton counits in abelian categories

@stack 018U

The counit of a simplicial skeleton is monic in an abelian category.  This file owns both the
objectwise instance and its natural-transformation counterpart, so downstream constructions can
work at the level appropriate to their morphisms without importing generated-subobject APIs.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Skeleton

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The component of a simplicial skeleton counit is monic in an abelian category. -/
@[stacks 018U "the simplicial skeleton counit is a monomorphism"]
instance counit.mono (n : ℕ) (U : SimplicialObject A) :
    Mono ((skAdj n).counit.app U) := sorry

/-- The simplicial skeleton counit is a monomorphism of endofunctors in an abelian category. -/
@[stacks 018U "the natural simplicial skeleton counit is a monomorphism"]
instance counit.natMono (n : ℕ) :
    Mono ((skAdj (C := A) n).counit) := sorry

end CategoryTheory.SimplicialObject.Skeleton
