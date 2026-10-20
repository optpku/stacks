/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cover.Pullback

/-!
# Pullback-cover restriction recall

Restriction compatibility is the functorial transport of arrows and relations
between pullback covers in a slice; it is independent of the Chapter 7 sheaf
construction.
-/

@[expose] public section

#check @CategoryTheory.GrothendieckTopology.Cover.Arrow.mapOver
#check @CategoryTheory.GrothendieckTopology.Cover.Arrow.mapOver_comp
#check @CategoryTheory.GrothendieckTopology.Cover.Relation.mapOver
#check @CategoryTheory.GrothendieckTopology.Cover.Relation.mapOver_comp
