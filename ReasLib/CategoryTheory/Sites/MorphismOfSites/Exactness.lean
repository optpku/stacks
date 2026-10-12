/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Sheafification.AddCommGrp
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact inverse image for morphisms of sites

This leaf records the additive exactness consequence of the canonical
inverse-image functor of a morphism of sites.  The statement is independent
of ringed sites and keeps the coefficient universe separate from both site
universes.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor.IsMorphismOfSites

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The inverse image along a morphism of sites is exact on sheaves of abelian groups. -/
@[stacks 04JC "(1)"]
theorem abelianPullback_exact
    (u : C ⥤ D) [IsMorphismOfSites J K u]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P]
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}]
    [PreservesFiniteLimits
      (u.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{w})] :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})
      (u.sheafPullback AddCommGrpCat.{w} J K) := sorry

end CategoryTheory.Functor.IsMorphismOfSites
