/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory GrothendieckTopology CategoryTheory.Limits

universe u v

/- Definition 7.32.2: a point of a site with covering precoverage K is a functor
F : C ⥤ Type (max u v) such that covering families are jointly surjective on F,
covering pullback comparisons F(Uᵢ ×_U V) → F(Uᵢ) ×_{F(U)} F(V) are bijective,
and the canonical stalk functor on sheaves for K.toGrothendieck is left exact.
The site axioms require pullbacks only along covering arrows. -/
@[stacks 00Y5] #check
  (CategoryTheory.Precoverage.IsSitePoint :
    ∀ {C : Type u} [Category.{v} C] (K : Precoverage C)
      [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange]
      [K.HasPullbacks] (F : C ⥤ Type (max u v)), Prop)
