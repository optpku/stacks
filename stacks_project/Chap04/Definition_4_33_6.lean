/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {S : Type u₁} [Category.{v₁} S]
variable {C : Type u₂} [Category.{v₂} C]
variable {p : S ⥤ C} (χ : p.Cleavage)
variable {U V : C} (f : V ⟶ U)

/- Definition 4.33.6 (1): a cleavage of `p : S ⥤ C` chooses a strongly cartesian lift of every
morphism `f : V ⟶ p.obj x`. The intrinsic data owner does not depend on a chosen presentation of
the fibres. -/
@[stacks 02XN "cleavage by chosen strongly cartesian lifts"]
#check (Functor.Cleavage p : Type max u₁ u₂ v₁ v₂)

/- Companion recall: one chosen lift bundles its source, total-category arrow, and strongly
cartesian universal property. -/
#check Functor.StronglyCartesianLift

/- Definition 4.33.6 (2): a cleavage induces a reindexing functor between the standard fibres. -/
@[stacks 02XN "reindexing functor induced on standard fibers"]
#check (Functor.Cleavage.reindex χ f : Functor.Fiber p U ⥤ Functor.Fiber p V)

end CategoryTheory
