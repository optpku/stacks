module

public import ReasLib.CategoryTheory.Sites.Cover.Pullback
public import ReasLib.CategoryTheory.Sites.Descent.HomSheaf.Localized

/-!
# Source restriction-section recall

The direct source-side section calculations are instances of cover-arrow
transport and localized Hom restriction, which are independent of the former
Chapter 7 construction.
-/

@[expose] public section

#check @CategoryTheory.GrothendieckTopology.Cover.Arrow.mapOver_base
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.restrict
#check @CategoryTheory.GrothendieckTopology.LocalizedHom.terminalArrow
