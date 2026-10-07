module

public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import ReasLib.Topology.Sheaf.Pushforward
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global sections with support in a closed subset

This file owns the underived global-sections-with-support functor for abelian sheaves. It is the
canonical composite of the closed-support functor, pushforward from the closed subspace, and
global sections on the ambient space.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.ClosedSubset.GlobalSectionsWithSupport

variable {X : TopCat.{u}} {Z : Set X}

/-- Global sections with support in the closed subset `Z` of an abelian sheaf. -/
@[stacks 0A39 "global sections with support in a closed subset"]
abbrev functor (hZ : IsClosed Z) : X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  SectionsWithSupport.functor hZ ⋙
    Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z) ⋙
    CategoryTheory.Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- Global sections with support form an additive functor for the current preadditive structures. -/
instance functor_additive [Preadditive (X.Sheaf AddCommGrpCat.{u})]
    [Preadditive AddCommGrpCat.{u}] (hZ : IsClosed Z) : (functor hZ).Additive := sorry

end TopCat.Sheaf.ClosedSubset.GlobalSectionsWithSupport
