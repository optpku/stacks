/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Extension.Derived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded cohomological devissage

A two-sided bounded derived object is assembled from finitely many shifted cohomology objects.
Consequently, membership in any retract-stable property closed under finite coproducts and middle
terms of distinguished triangles can be detected on the degree-`q` single of its `q`-th
cohomology object.  No shift-stability assumption on the property is needed.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.BoundedDevissage

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- A derived object supported in `[a, b]` belongs to `P` when the correctly shifted singles of
its cohomology objects in that interval belong to `P`. -/
@[stacks 0FX7 "bounded cohomological devissage"]
theorem mem (P : ObjectProperty (DerivedCategory A))
    [P.IsStableUnderRetracts] [P.IsClosedUnderFiniteCoproducts]
    [P.IsTriangulatedClosed₂] (K : DerivedCategory A) (a b : ℤ)
    (hGE : K.IsGE a) (hLE : K.IsLE b)
    (hH : ∀ q : Set.Icc a b,
      P ((DerivedCategory.singleFunctor A q.1).obj
        ((DerivedCategory.homologyFunctor A q.1).obj K))) :
    P K := sorry

/-- Existential-bounds form of bounded cohomological devissage. -/
@[stacks 0FX7 "bounded cohomological devissage with existential bounds"]
theorem mem_of_homology (P : ObjectProperty (DerivedCategory A))
    [P.IsStableUnderRetracts] [P.IsClosedUnderFiniteCoproducts]
    [P.IsTriangulatedClosed₂] (K : DerivedCategory A)
    (hbounded : ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b)
    (hH : ∀ q : ℤ,
      P ((DerivedCategory.singleFunctor A q).obj
        ((DerivedCategory.homologyFunctor A q).obj K))) :
    P K := sorry

end CategoryTheory.DerivedCategory.BoundedDevissage
