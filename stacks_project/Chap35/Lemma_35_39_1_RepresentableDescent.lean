/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Representable

/-!
# Representable descent on a subcanonical site

This compatibility module exposes the reusable representable-descent API to existing
source-facing consumers.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.GrothendieckTopology.RepresentableDescent

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C) [J.Subcanonical]
variable {S : C} {I : Type (max u v)} {X : I → C} (p : ∀ i, X i ⟶ S)

/- The explicit gluing functor sends slice descent data to sheaves locally representable
along the covering family. -/
#check (glue J p :
  (hcover : Sieve.ofArrows X p ∈ J S) →
    Over.pseudofunctor.DescentData p ⥤ LocallyRepresentableAlong J p)

end CategoryTheory.GrothendieckTopology.RepresentableDescent
