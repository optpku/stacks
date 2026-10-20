/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cover.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized

/-!
# Glue restriction-presheaf recall

The reusable public interface is compatibility of local Hom morphisms and its
unique glueing theorem; bookkeeping of a particular source presentation is
not retained as an API.
-/

@[expose] public section

#check @CategoryTheory.GrothendieckTopology.LocalizedHom.Compatible
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.existsUnique_of_compatible
#check @CategoryTheory.GrothendieckTopology.Cover.Relation.mapOver
