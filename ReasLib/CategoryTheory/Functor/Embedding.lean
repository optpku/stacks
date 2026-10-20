/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Equality-sensitive embeddings of categories

This file provides the presentation-level notion of an embedding of categories: the object map
is injective and the functor is faithful on morphisms. Fullness is deliberately not part of the
definition, so inclusions of non-full subcategories can satisfy it.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-- A functor is an embedding when it is injective on objects and faithful on morphisms.

This is an equality-sensitive property of a chosen presentation of the source and target
categories, rather than an equivalence-invariant substitute for full faithfulness. -/
@[stacks 05QM]
class IsEmbedding (F : C ⥤ D) : Prop extends F.Faithful where
  /-- Distinct source objects remain distinct in the target. -/
  obj_injective : Function.Injective F.obj

attribute [instance] IsEmbedding.toFaithful

/-- A functor is an embedding exactly when its object map is injective and it is faithful. -/
theorem isEmbedding_iff (F : C ⥤ D) :
    F.IsEmbedding ↔ Function.Injective F.obj ∧ F.Faithful := sorry

namespace IsEmbedding

/-- The identity functor is an embedding. -/
instance id : (𝟭 C).IsEmbedding := sorry

variable {F : C ⥤ D} {G : D ⥤ E}

/-- A composite of embeddings is an embedding. -/
instance comp [F.IsEmbedding] [G.IsEmbedding] : (F ⋙ G).IsEmbedding := sorry

end IsEmbedding

end CategoryTheory.Functor
