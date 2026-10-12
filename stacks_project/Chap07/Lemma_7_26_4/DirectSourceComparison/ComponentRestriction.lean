/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cover.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized

/-!
# Component restriction recall

Restriction of component data uses the generic slice transport of pullback
cover arrows and the localized Hom restriction interface.
-/

@[expose] public section

#check @CategoryTheory.GrothendieckTopology.Cover.Arrow.mapOver
#check @CategoryTheory.GrothendieckTopology.Cover.Relation.mapOver
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.restrict
