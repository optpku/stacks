/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.FiniteLimits
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton.Simplicial
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback-compatible singleton replacements

This file packages the condition that taking coproducts of the sources of fixed-target formal
coproducts commutes with pullbacks.  The instance also supplies the coproduct of each resulting
pullback family, so downstream matching-object constructions do not need local instance pins.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Limits

namespace Limits.FormalCoproduct.Over.CoproductSingleton

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- Fixed-target singleton-coproduct replacement is pullback-compatible when pullback families
have source coproducts and the induced square of singleton replacements is a pullback square. -/
@[stacks 0DB2 "coproducts commute with pullbacks"]
class PullbackCompatible (X : C) : Prop where
  /-- A pullback family has a coproduct of its source objects whenever the three input families
  do. -/
  hasCoproduct :
    ∀ {K L M : FormalCoproduct.{w} (CategoryTheory.Over X)}
      [HasCoproduct (fun i ↦ (K.obj i).left)]
      [HasCoproduct (fun i ↦ (L.obj i).left)]
      [HasCoproduct (fun i ↦ (M.obj i).left)]
      (f : K ⟶ M) (g : L ⟶ M),
      HasCoproduct (fun i ↦ ((pullback f g).obj i).left)
  /-- Taking the coproducts of sources carries a formal-coproduct pullback square to a pullback
  square. -/
  isPullback :
    ∀ {K L M : FormalCoproduct.{w} (CategoryTheory.Over X)}
      [HasCoproduct (fun i ↦ (K.obj i).left)]
      [HasCoproduct (fun i ↦ (L.obj i).left)]
      [HasCoproduct (fun i ↦ (M.obj i).left)]
      (f : K ⟶ M) (g : L ⟶ M),
      ∀ [HasCoproduct (fun i ↦ ((pullback f g).obj i).left)],
      IsPullback
        (Over.coproductSingletonMap (pullback.fst f g))
        (Over.coproductSingletonMap (pullback.snd f g))
        (Over.coproductSingletonMap f)
        (Over.coproductSingletonMap g)

attribute [instance] PullbackCompatible.hasCoproduct

/-- Pullback compatibility is exactly coproduct existence for pullback families together with
the assertion that singleton replacement carries every such square to a pullback square. -/
theorem pullbackCompatible_iff (X : C) :
    PullbackCompatible.{w} X ↔
      (∀ {K L M : FormalCoproduct.{w} (CategoryTheory.Over X)}
          [HasCoproduct (fun i ↦ (K.obj i).left)]
          [HasCoproduct (fun i ↦ (L.obj i).left)]
          [HasCoproduct (fun i ↦ (M.obj i).left)]
          (f : K ⟶ M) (g : L ⟶ M),
          HasCoproduct (fun i ↦ ((pullback f g).obj i).left)) ∧
        (∀ {K L M : FormalCoproduct.{w} (CategoryTheory.Over X)}
          [HasCoproduct (fun i ↦ (K.obj i).left)]
          [HasCoproduct (fun i ↦ (L.obj i).left)]
          [HasCoproduct (fun i ↦ (M.obj i).left)]
          (f : K ⟶ M) (g : L ⟶ M),
          ∀ [HasCoproduct (fun i ↦ ((pullback f g).obj i).left)],
            IsPullback
              (Over.coproductSingletonMap (pullback.fst f g))
              (Over.coproductSingletonMap (pullback.snd f g))
              (Over.coproductSingletonMap f)
              (Over.coproductSingletonMap g)) := sorry

end Limits.FormalCoproduct.Over.CoproductSingleton

end CategoryTheory
