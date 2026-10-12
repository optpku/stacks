/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Presheaf
public import ReasLib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective preservation for fiber-presheaf reindexing

This leaf isolates the projective hypothesis used by derived category homology. The underlying
restriction and reindexing operations remain independent of projective objects.
-/

@[expose] public section

open CategoryTheory

universe u v w vS a b

namespace CategoryTheory.FiberedCategoryOver.Presheaf

variable {C : Type u} [Category.{v} C]
variable (X : FiberedCategoryOver.{u, v, w, vS} C)
variable (A : Type a) [Category.{b} A]

/-- The property that every fiber-presheaf reindexing functor preserves projective objects. -/
@[stacks 08PH "projective preservation for derived fiber homology"]
class PreservesProjectiveReindex : Prop where
  /-- Reindexing along any base arrow preserves projective objects. -/
  preserves {U V : C} (f : V ⟶ U) : (reindex X A f).PreservesProjectiveObjects

/-- Build the reindexing-preservation instance from its pointwise mathematical content. -/
@[stacks 08PH "pointwise projective preservation constructor"]
abbrev PreservesProjectiveReindex.of_forall
    (h : ∀ ⦃U V : C⦄ (f : V ⟶ U), (reindex X A f).PreservesProjectiveObjects) :
    PreservesProjectiveReindex X A :=
  ⟨fun {_ _} f => h f⟩

/-- Reindexing along a fixed base arrow preserves projective objects. -/
@[stacks 08PH "projective preservation for one reindexing"]
instance (priority := 100) preservesProjectiveObjects
    [h : PreservesProjectiveReindex X A] {U V : C} (f : V ⟶ U) :
    (reindex X A f).PreservesProjectiveObjects :=
  h.preserves f

end CategoryTheory.FiberedCategoryOver.Presheaf
