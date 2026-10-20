/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.StrongTrans
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack

/-!
# The stack condition for fibered categories

A fibered category `p : S ⥤ C` is a stack over a site `(C, J)` when its canonical fiber
pseudofunctor satisfies the stack condition.  Descent-data transport is owned by the generic
indexed-functor API; this file keeps only the site-theoretic stack condition and its thin
strong-transformation specialization.

## Main declarations

* `CategoryTheory.IsStack.OnSite` — the site-theoretic stack condition on a projection functor.
* `CategoryTheory.Pseudofunctor.StrongTrans.descentFunctor` — the tagged specialization of
  `IndexedFunctor.mapDescentData`.
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-! ## The stack condition -/

/-- A stack over the site `(C, J)` is a category over `C` whose projection is fibered and whose
canonical pseudofunctor of fibers is a stack for `J`; this packages both the sheaf condition on
the presheaves `Hom(x, y)` and the effectiveness of descent data. -/
@[stacks 026F]
class IsStack.OnSite (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends p.IsFibered, Pseudofunctor.IsStack (Functor.fiberPseudofunctor p) J

attribute [stacks 026F "stack fibredness field"] IsStack.OnSite.toIsFibered
attribute [stacks 026F "stack pseudofunctor field"] IsStack.OnSite.toIsStack

/-- Once fibredness is fixed, the projection-level stack condition is exactly the canonical
Mathlib stack condition on the fibre pseudofunctor. -/
@[stacks 026F "stack defining conditions"]
theorem IsStack.OnSite.iff_stack
    (J : GrothendieckTopology C) (p : S ⥤ C) [p.IsFibered] :
    IsStack.OnSite J p ↔
      Pseudofunctor.IsStack (Functor.fiberPseudofunctor p) J := sorry

/-- Every stack on a site is canonically a prestack on that site.  This named projection-level
instance exposes the Hom-sheaf half of effective descent without rebuilding the fibre
pseudofunctor at a use site. -/
@[stacks 026F "stack-to-prestack bridge"]
instance IsStack.OnSite.toPrestack
    {J : GrothendieckTopology C} {p : S ⥤ C} [IsStack.OnSite J p] :
    IsPrestack.OnSite J p := sorry

/-- A fibered category whose fiber pseudofunctor is already a stack for `J` is canonically a
stack over the site `(C, J)`. -/
@[stacks 026F "canonical stack instance from the fibre pseudofunctor"]
instance (J : GrothendieckTopology C) (p : S ⥤ C) [p.IsFibered]
    [Pseudofunctor.IsStack (Functor.fiberPseudofunctor p) J] : IsStack.OnSite J p where
  toIsFibered := inferInstance
  toIsStack := inferInstance

/-! ## Descent transport -/

namespace Pseudofunctor.StrongTrans

open Opposite

variable {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₂, u₂}}
variable (η : Pseudofunctor.StrongTrans F G)
variable {ι : Type w} {U : C} {X : ι → C} (f : ∀ i, X i ⟶ U)

/-- A strong transformation acts on descent-data categories through the canonical indexed-functor
bridge and the generic `mapDescentData` owner. -/
@[stacks 026F "descent functor induced by a strong transformation"]
noncomputable abbrev descentFunctor : F.DescentData f ⥤ G.DescentData f :=
  η.toIndexedFunctor.mapDescentData f

end Pseudofunctor.StrongTrans

end CategoryTheory
