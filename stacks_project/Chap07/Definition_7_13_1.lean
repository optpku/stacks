/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.IndexedSite.Continuous
import StacksCheckRecall

@[expose] public section

universe w uC uD vC vD

open CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/- Definition 7.13.1: a functor u : C ⥤ D of sites is continuous when every
selected indexed covering family {Vᵢ ⟶ V} of C maps to a selected covering
family {u(Vᵢ) ⟶ u(V)} of D, and for every T ⟶ V the canonical comparison
u(T ×_V Vᵢ) ⟶ u(T) ×_{u(V)} u(Vᵢ) is an isomorphism. -/
@[stacks 00WV] #check (CategoryTheory.PreZeroHypercover.IsContinuous :
  C ⥤ D → ∀ (J : ∀ target : C, Set (CategoryTheory.PreZeroHypercover.{w} target))
    (K : ∀ target : D, Set (CategoryTheory.PreZeroHypercover.{w} target)),
    [CategoryTheory.PreZeroHypercover.IsSite J] →
    [CategoryTheory.PreZeroHypercover.IsSite K] → Prop)
