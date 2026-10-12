/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Over.Flat
public import ReasLib.CategoryTheory.Sites.Over.Continuity
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of sites on slice categories

This leaf upgrades the categorical slice-flatness theorem and the established
slice-continuity theorem to the site-level morphism-of-sites interface.
-/

@[expose] public section

universe uC vC uD vD

namespace CategoryTheory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

/-- Lemma 7.28.1: a morphism of sites remains a morphism of sites after
passing to the slice sites over an object and its image. -/
@[stacks 03CF]
theorem IsMorphismOfSites.overPost
    (u : C ⥤ D) {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [IsMorphismOfSites J K u] (U : C) :
    IsMorphismOfSites (J.over U) (K.over (u.obj U)) (Over.post (X := U) u) := sorry

end CategoryTheory
