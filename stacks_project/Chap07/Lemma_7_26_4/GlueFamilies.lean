/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Canonical
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized

/-!
# Compatible-family glueing recall

The old fixed-cover family subtype was specific to one proof.  Reusable local
compatibility and unique glueing are provided by `LocalizedHom`, while overlap
comparison belongs to canonical family descent data.
-/

@[expose] public section

#check @CategoryTheory.GrothendieckTopology.LocalizedHom.Compatible
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.existsUnique_of_compatible
#check @CategoryTheory.DescentDatum.Canonical.overlapIso
