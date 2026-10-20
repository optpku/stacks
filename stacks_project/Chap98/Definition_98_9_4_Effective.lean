/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective
public import stacks_project.Chap98.«98_9_3_1»

/-!
# Effective formal objects

A formal object of a category fibred in groupoids over `(Sch/S)_fppf` is
effective when it lies in the essential image of the approximation functor
from complete local objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.IsEffective :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S},
    GroupoidsOver.FormalObject X → Prop)

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.instIsEffective_obj :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    (x : GroupoidsOver.CompleteLocalObject X),
    GroupoidsOver.FormalObject.IsEffective ((GroupoidsOver.approximation X).obj x))

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.isEffective_iff :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {ξ : GroupoidsOver.FormalObject X},
    GroupoidsOver.FormalObject.IsEffective ξ ↔ (GroupoidsOver.approximation X).essImage ξ)

#check (AlgebraicGeometry.GroupoidsOver.FormalObject.isEffective_iff_exists :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {ξ : GroupoidsOver.FormalObject X},
    GroupoidsOver.FormalObject.IsEffective ξ ↔
      ∃ x : GroupoidsOver.CompleteLocalObject X,
        Nonempty ((GroupoidsOver.approximation X).obj x ≅ ξ))
