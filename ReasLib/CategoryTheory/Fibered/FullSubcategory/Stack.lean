/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.FullSubcategory.Fiber
public import ReasLib.CategoryTheory.Fibered.Stack.Basic
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Choice.Basic

@[expose] public section

/-!
# Stack criteria for full subcategories

This module owns the reusable criterion behind the full-subcategory stack argument.  The
property is stated on the inverse image in each fiber, so it is independent of a particular
cover presentation or of any auxiliary descent-data transport construction.
-/

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open Functor Functor.Fiber

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]

namespace ObjectProperty

/-! ## Fiberwise closure predicates -/

/-- The fiberwise inverse image of an object property `P` over an object `U : C`. -/
def fiber (P : ObjectProperty X) (p : X ⥤ C) (U : C) : ObjectProperty (p.Fiber U) :=
  P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)

namespace IsStableUnder

/-- `P` is stable under every strongly cartesian pullback, up to isomorphism in the source
fiber. This choice-free predicate is the canonical owner of pullback stability. -/
@[stacks 04TU "choice-free cartesian pullback stability"]
def CartesianPullback (P : ObjectProperty X) (p : X ⥤ C) : Prop :=
  ∀ ⦃R S : C⦄ (f : R ⟶ S) ⦃a b : X⦄ (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] (_ : P b),
    (P.fiber p R).isoClosure
      (⟨a, IsHomLift.domain_eq p f φ⟩ : p.Fiber R)

/-- Stability under the pullbacks selected by the canonical cleavage, expressed fiberwise. -/
def Pullback (P : ObjectProperty X) (p : X ⥤ C) [p.IsFibered] : Prop :=
  ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_ : P x.1),
    (P.fiber p V).isoClosure (f⁎[Functor.Cleavage.ofIsFibered p] x)

/-- For a fibered projection, choice-free cartesian stability is equivalent to stability under
the pullbacks selected by the canonical cleavage. -/
theorem cartesianPullback_iff_pullback
    (P : ObjectProperty X) (p : X ⥤ C) [p.IsFibered] :
    CartesianPullback P p ↔ Pullback P p := sorry

end IsStableUnder

namespace Fiberwise

/-- The fiberwise `isoClosure` of `P` is local for the covering topology `J`, with reindexing
computed by the specified cleavage. This is the choice-parametric owner of fiberwise locality. -/
@[stacks 04TU "choice-parametric fiberwise locality"]
def IsLocal (P : ObjectProperty X) (J : GrothendieckTopology C)
    {p : X ⥤ C} (chi : p.Cleavage) : Prop :=
  ∀ ⦃U : C⦄ (S : J.Cover U) (x : p.Fiber U)
    (_ : ∀ I : S.Arrow, (P.fiber p I.Y).isoClosure (I.f⁎[chi] x)),
    (P.fiber p U).isoClosure x

/-- Fiberwise locality is independent of the cleavage used to compute reindexing. -/
theorem IsLocal.iff_of_cleavage
    (P : ObjectProperty X) (J : GrothendieckTopology C)
    {p : X ⥤ C} (chi₁ chi₂ : p.Cleavage) :
    IsLocal P J chi₁ ↔ IsLocal P J chi₂ := sorry

end Fiberwise

/-- The canonical-cleavage specialization of fiberwise locality. -/
@[stacks 04TU "canonical fiberwise locality"]
def IsFiberwiseLocal (P : ObjectProperty X) (J : GrothendieckTopology C)
    (p : X ⥤ C) [p.IsFibered] : Prop :=
  Fiberwise.IsLocal P J (Functor.Cleavage.ofIsFibered p)

/-- The canonical fiberwise-locality predicate agrees with the formulation for any specified
cleavage. -/
theorem IsFiberwiseLocal.iff_for
    (P : ObjectProperty X) (J : GrothendieckTopology C)
    (p : X ⥤ C) [p.IsFibered] (chi : p.Cleavage) :
    P.IsFiberwiseLocal J p ↔ Fiberwise.IsLocal P J chi := sorry

namespace FullSubcategory

/-- A full subcategory cut out by a property stable under strongly cartesian pullback is again
fibred over the same base.  This topology-free result is the structural layer used by the later
stack criterion. -/
@[stacks 04TU "fibredness of a cartesian-stable full subcategory"]
theorem isFibered
    (P : ObjectProperty X) (p : X ⥤ C) [p.IsFibered]
    (hP : IsStableUnder.CartesianPullback P p) :
    (P.ι ⋙ p).IsFibered := sorry

/-! ## The stack criterion -/

/-- A full subcategory of a stack remains a stack when its defining property is stable under
fiberwise cartesian pullback and its fiberwise iso-closure is local for the covering topology. -/
@[stacks 04TU]
theorem isStackOnSite
    (J : GrothendieckTopology C) (p : X ⥤ C) (P : ObjectProperty X)
    [IsStack.OnSite J p]
    (hpullback : IsStableUnder.CartesianPullback P p)
    (hlocal : P.IsFiberwiseLocal J p) :
    IsStack.OnSite J (P.ι ⋙ p) := sorry

end FullSubcategory
end ObjectProperty

/-! ## Stable public checks -/

end CategoryTheory
