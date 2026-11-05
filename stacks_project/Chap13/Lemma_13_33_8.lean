/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Homological
import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.33.8

The textbook statement is the homological-functor image of a sequential
homotopy colimit.  Its canonical owner is the generic sequential diagram API,
not a chosen family `K n`, successor maps, and a particular telescope
triangle.  The presentation-level declarations below remain available when
concrete cocone legs or the comparison map are needed.

The tagged intrinsic result is
`CategoryTheory.HomotopyColimit.IsOf.existsImageIsColimit`. Its local hypotheses require
preservation of the coproducts of both the diagram terms and their shifts by one;
commuting with all countable coproducts supplies these hypotheses in Stacks 0CRK.
-/

#check @CategoryTheory.HomotopyColimit.Presentation.imageCocone
#check @CategoryTheory.HomotopyColimit.Presentation.toCocone
#check @CategoryTheory.HomotopyColimit.Presentation.triangle
#check @CategoryTheory.HomotopyColimit.Presentation.ofTriangle
#check @CategoryTheory.HomotopyColimit.Presentation.ofLegs.ι
#check @CategoryTheory.HomotopyColimit.Presentation.ofTriangle.connecting
#check @CategoryTheory.HomotopyColimit.Presentation.ofCoproductTriangle
#check @CategoryTheory.HomotopyColimit.Presentation.ofCoproductTriangle.ι
#check @CategoryTheory.HomotopyColimit.Presentation.ofCoproductTriangle.connecting
#check @CategoryTheory.HomotopyColimit.Presentation.ofCoproductTriangle.toCocone
#check @CategoryTheory.HomotopyColimit.Presentation.imageCocone_pt
#check @CategoryTheory.HomotopyColimit.Presentation.imageCocone_ι_app
#check @CategoryTheory.HomotopyColimit.Presentation.imageComparison
#check @CategoryTheory.HomotopyColimit.Presentation.colimit_ι_comp_imageComparison
#check @CategoryTheory.HomotopyColimit.Presentation.ImageCocone.nonemptyIsColimit
#check @CategoryTheory.HomotopyColimit.Presentation.ImageCocone.nonemptyIsColimitOfPreserves
#check @CategoryTheory.HomotopyColimit.Presentation.ImageComparison.isIso
#check @CategoryTheory.HomotopyColimit.Presentation.Hom.triangleMorphism
#check @CategoryTheory.HomotopyColimit.Presentation.Hom.imageCoconeHom
#check @CategoryTheory.HomotopyColimit.Presentation.Hom.imageComparison_naturality
#check @CategoryTheory.HomotopyColimit.Presentation.ImageCocone.map
#check @CategoryTheory.HomotopyColimit.Presentation.ImageComparison.natTrans_naturality
@[stacks 0CRK] #check @CategoryTheory.HomotopyColimit.IsOf.existsImageIsColimit
