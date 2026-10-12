/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Topology on costructured arrow categories

For a functor `u : C ⥤ D`, an object `V : D`, and a Grothendieck topology `J` on `C`,
the costructured arrow category `CostructuredArrow u V` inherits a topology whose covers
are detected by pushforward along the projection to `C`.

This generalizes the restricted topology to the comma category setting.
-/

@[expose] public section

open CategoryTheory Limits

universe u₁ u₂ v₁ v₂

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (u : C ⥤ D) (V : D)

/-- The Grothendieck topology on `CostructuredArrow u V` whose covering sieves are
those whose pushforward along the projection to `C` is a `J`-cover. -/
def cocontinuousOverTopology : GrothendieckTopology (CostructuredArrow u V) where
  sieves X S := Sieve.functorPushforward (CostructuredArrow.proj u V) S ∈ J X.left
  top_mem' := sorry
  pullback_stable' := sorry
  transitive' := sorry

namespace cocontinuousOverTopology

/-- The projection preserves covering sieves. -/
theorem coverPreserving :
    CoverPreserving (cocontinuousOverTopology J u V) J (CostructuredArrow.proj u V) := sorry

/-- The projection preserves compatible families. -/
theorem compatiblePreserving :
    CompatiblePreserving J (CostructuredArrow.proj u V) := sorry

/-- The projection is continuous. -/
instance isContinuous :
    Functor.IsContinuous (CostructuredArrow.proj u V)
      (cocontinuousOverTopology J u V) J := sorry

end cocontinuousOverTopology

end CategoryTheory
