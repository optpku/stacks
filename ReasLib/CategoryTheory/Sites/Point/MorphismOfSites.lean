/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Comap
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of site points along morphisms of sites

This file packages Mathlib's point-comap construction behind the project-level
`IsMorphismOfSites` owner.  It also exposes the resulting comparison of sheaf fibers uniformly
in the coefficient category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v

namespace CategoryTheory.GrothendieckTopology.Point

variable {C D : Type*} [Category* C] [Category* D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (p : Point.{w} K) (F : C ⥤ D) [hF : IsMorphismOfSites J K F]
variable [h_small : InitiallySmall (F ⋙ p.fiber).Elements]

/-- The canonical comap of a point along a morphism of sites. Continuity, cover preservation,
and representable flatness are inferred from `IsMorphismOfSites`. -/
@[stacks 05V5 "site point comap"]
abbrev comapOfMorphismOfSites : Point.{w} J :=
  p.comap F (CoverPreserving.of_isContinuous F J K)

variable (A : Type*) [Category.{v} A] [Limits.HasProducts.{w} A]
variable [h_adj : (F.sheafPushforwardContinuous A J K).IsRightAdjoint]
variable [Limits.HasColimitsOfSize.{w, w} A]

/-- Sheaf fiber at the comapped point is canonically isomorphic to sheaf pullback followed by
the original fiber functor. -/
@[stacks 05V5 "sheaf fiber comap"]
noncomputable abbrev sheafFiberComapIsoOfMorphismOfSites :
    (p.comapOfMorphismOfSites F).sheafFiber ≅
      F.sheafPullback A J K ⋙ p.sheafFiber :=
  p.sheafFiberComapIso F (CoverPreserving.of_isContinuous F J K) A

end CategoryTheory.GrothendieckTopology.Point
