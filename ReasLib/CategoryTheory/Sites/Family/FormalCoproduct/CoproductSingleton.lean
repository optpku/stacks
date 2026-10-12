/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton.Pullback
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Covering
public import ReasLib.CategoryTheory.Sites.MorphismProperty.Covering
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cover-preserving singleton replacements

This file packages the topology-relative condition that a covering morphism of formal coproduct
families induces a covering arrow between their coproduct objects.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Limits

namespace Limits.FormalCoproduct.CoproductSingleton

variable {C : Type u} [Category.{v} C]

/-- Singleton-coproduct replacement preserves covering morphisms when the induced map between
the two coproduct objects is a covering arrow for `J`. -/
@[stacks 0DB2 "coproduct maps preserve coverings"]
class PreservesCovering (J : GrothendieckTopology C) : Prop where
  /-- A covering formal-coproduct morphism induces a covering arrow on coproducts. -/
  map {K L : FormalCoproduct.{w} C}
    [HasCoproduct K.obj] [HasCoproduct L.obj] (φ : K ⟶ L) :
    SemiRepresentableFamily.covering J φ →
      J.coveringArrows (FormalCoproduct.coproductMap φ)

/-- A singleton-replacement morphism is covering exactly when its sole coproduct component is a
covering arrow. -/
theorem coproductSingletonMap_isCovering_iff
    (J : GrothendieckTopology C) {K L : FormalCoproduct.{w} C}
    [HasCoproduct K.obj] [HasCoproduct L.obj] (φ : K ⟶ L) :
    SemiRepresentableFamily.covering J
        (FormalCoproduct.coproductSingletonMap φ) ↔
      J.coveringArrows (FormalCoproduct.coproductMap φ) := sorry

/-- Cover preservation turns a covering family morphism into a covering morphism between its
singleton-coproduct replacements. -/
theorem map_isCovering (J : GrothendieckTopology C) [PreservesCovering.{w} J]
    {K L : FormalCoproduct.{w} C} [HasCoproduct K.obj] [HasCoproduct L.obj]
    (φ : K ⟶ L) (hφ : SemiRepresentableFamily.covering J φ) :
    SemiRepresentableFamily.covering J
      (FormalCoproduct.coproductSingletonMap φ) := sorry

/-- The cover-preservation property applies to a fixed-target formal-coproduct morphism after
forgetting the common target. -/
theorem map_over (J : GrothendieckTopology C) [PreservesCovering.{w} J]
    {X : C} {K L : FormalCoproduct.{w} (CategoryTheory.Over X)}
    [HasCoproduct (fun i ↦ (K.obj i).left)]
    [HasCoproduct (fun i ↦ (L.obj i).left)]
    (φ : K ⟶ L) (hφ : SemiRepresentableFamily.OverFamily.covering J φ) :
    J.coveringArrows (FormalCoproduct.Over.coproductSingletonMapLeft φ) := sorry

/-- Cover preservation turns a covering fixed-target family morphism into a covering morphism
between its fixed-target singleton-coproduct replacements. -/
theorem map_over_isCovering (J : GrothendieckTopology C) [PreservesCovering.{w} J]
    {X : C} {K L : FormalCoproduct.{w} (CategoryTheory.Over X)}
    [HasCoproduct (fun i ↦ (K.obj i).left)]
    [HasCoproduct (fun i ↦ (L.obj i).left)]
    (φ : K ⟶ L) (hφ : SemiRepresentableFamily.OverFamily.covering J φ) :
    SemiRepresentableFamily.OverFamily.covering J
      (FormalCoproduct.Over.coproductSingletonMap φ) := sorry

end Limits.FormalCoproduct.CoproductSingleton

end CategoryTheory
