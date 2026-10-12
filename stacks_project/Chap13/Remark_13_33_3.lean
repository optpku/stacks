/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.33.3

Maps between telescope presentations are represented by the composable
structure `HomotopyColimit.Presentation.Hom` rather than a bare existential.
-/

@[stacks 0CRI] #check @CategoryTheory.HomotopyColimit.Presentation.nonemptyHom

#check @CategoryTheory.HomotopyColimit.Presentation.Hom
#check @CategoryTheory.HomotopyColimit.Presentation.Hom.id
#check @CategoryTheory.HomotopyColimit.Presentation.Hom.comp
#check @CategoryTheory.HomotopyColimit.Presentation.Hom.toCocone_naturality
#check @CategoryTheory.HomotopyColimit.Presentation.Hom.connecting_naturality
#check @CategoryTheory.HomotopyColimit.Presentation.Hom.ι_naturality
#check @CategoryTheory.HomotopyColimit.Presentation.Hom.coconeHom
#check @CategoryTheory.HomotopyColimit.Presentation.Hom.triangleMorphism
#check @CategoryTheory.HomotopyColimit.Presentation.existsStageMap
