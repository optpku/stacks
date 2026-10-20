/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Objects.Simplicial
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Basis
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise properties of terminal-presheaf hypercoverings

This leaf owns degreewise source-object predicates for site-level hypercoverings and the
existence theorem obtained from a basis of covering families.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace HypercoveringOf

/-- A site-level hypercovering lies degreewise in `B` when every component object in every
simplicial degree belongs to `B`. -/
abbrev degreewiseObjectsIn (K : HypercoveringOf.Terminal.{w} J) (B : Set C) : Prop :=
  FormalCoproduct.degreewiseObjectsIn K.simplicial B

/-- Unfolding `degreewiseObjectsIn` gives object membership in every ordinary simplicial
degree. -/
@[simp] theorem degreewiseObjectsIn_iff
    (K : HypercoveringOf.Terminal.{w} J) (B : Set C) :
    K.degreewiseObjectsIn B ↔
      ∀ n : ℕ,
        FormalCoproduct.objectsIn (K.simplicial.obj (op <| SimplexCategory.mk n)) B := sorry

namespace DegreewiseObjectsIn

/-- A degreewise object-membership condition supplies the condition in any chosen simplicial
degree. -/
theorem degree
    {K : HypercoveringOf.Terminal.{w} J} {B : Set C}
    (hK : K.degreewiseObjectsIn B) (n : ℕ) :
    FormalCoproduct.objectsIn (K.simplicial.obj (op <| SimplexCategory.mk n)) B := sorry

/-- Every component in a chosen degree of a degreewise hypercovering belongs to the designated
collection. -/
theorem mem
    {K : HypercoveringOf.Terminal.{w} J} {B : Set C}
    (hK : K.degreewiseObjectsIn B) (n : ℕ)
    (i : (K.simplicial.obj (op <| SimplexCategory.mk n)).I) :
    (K.simplicial.obj (op <| SimplexCategory.mk n)).obj i ∈ B := sorry

end DegreewiseObjectsIn

namespace Terminal

variable [Limits.HasEqualizers C] [Limits.HasPullbacks C]

/-- Lemma 25.12.3 (0DAX): a basis of covering families supplies a site-level hypercovering whose
objects lie degreewise in that basis. -/
@[stacks 0DAX "basis-valued hypercovering of a site"]
theorem exists_degreewiseObjectsIn
    (B : Set C)
    (hcover : ∀ U : C, ∃ 𝒰 : SR(C, U),
      𝒰.IsBasisCovering J.toPrecoverage B) :
    ∃ K : HypercoveringOf.Terminal.{w} J, K.degreewiseObjectsIn B := sorry

end Terminal
end HypercoveringOf
end CategoryTheory
