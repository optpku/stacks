/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor

/-!
# The prestack condition for fibered categories

A category fibered over a site is a prestack when its canonical fiber
pseudofunctor satisfies descent for morphisms.  This is the layer below
`IsStack.OnSite`: it records sheafness of all fiber Hom presheaves, without
requiring effectiveness of descent for objects.

## Main declarations

* `CategoryTheory.IsPrestack.OnSite` -- the prestack condition on a projection functor.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {J : GrothendieckTopology C} {p : S ⥤ C}

/-- A category over the site `(C, J)` is a prestack when its projection is fibered and its
canonical fiber pseudofunctor has sheaf Hom presheaves. -/
@[stacks 026F "prestack condition for a fibred category"]
class IsPrestack.OnSite (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends p.IsFibered, Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J

attribute [stacks 026F "prestack fibredness field"] IsPrestack.OnSite.toIsFibered
attribute [stacks 026F "prestack pseudofunctor field"] IsPrestack.OnSite.toIsPrestack

/-- Once fibredness is fixed, the projection-level prestack condition is exactly the canonical
Mathlib prestack condition on the fibre pseudofunctor. -/
@[stacks 026F "prestack defining conditions"]
theorem IsPrestack.OnSite.iff_prestack
    (J : GrothendieckTopology C) (p : S ⥤ C) [p.IsFibered] :
    IsPrestack.OnSite J p ↔
      Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J := sorry

/-- Fiberedness and the Mathlib prestack condition assemble into `IsPrestack.OnSite`. -/
@[stacks 026F "canonical prestack instance from the fibre pseudofunctor"]
instance (J : GrothendieckTopology C) (p : S ⥤ C) [p.IsFibered]
    [Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor p) J] : IsPrestack.OnSite J p where
  toIsFibered := inferInstance
  toIsPrestack := inferInstance

/-- The sheaf of morphisms between two fiber objects of a prestack, obtained directly from the
canonical Mathlib sheaf owner of the fiber pseudofunctor. -/
@[stacks 026A "prestack Hom sheaf"]
noncomputable abbrev IsPrestack.OnSite.sheafHom
    [IsPrestack.OnSite J p] {U : C} (x y : p.Fiber U) :
    Sheaf (J.over U) (Type v₂) :=
  (Functor.fiberPseudofunctor p).sheafHom J x y

end CategoryTheory
