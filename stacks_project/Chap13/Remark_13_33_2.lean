module

import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Uniqueness
import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Transport
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.33.2

The reusable owner is `HomotopyColimit.Presentation`, whose cocone and
connecting morphism retain exactly the data of a telescope presentation.
-/

@[stacks 0CRH] #check @CategoryTheory.HomotopyColimit.Presentation.nonemptyIso

#check @CategoryTheory.HomotopyColimit.Presentation.cocone
#check @CategoryTheory.HomotopyColimit.Presentation.ι_naturality
#check @CategoryTheory.HomotopyColimit.Presentation.Iso.ι_naturality
#check @CategoryTheory.HomotopyColimit.Presentation.ObjectIso.presentationIso
#check @CategoryTheory.HomotopyColimit.Presentation.DiagramIso.presentationIso
#check @CategoryTheory.HomotopyColimit.IsOf.nonemptyPresentation
#check @CategoryTheory.HomotopyColimit.IsOf.diagram
#check @CategoryTheory.HomotopyColimit.IsOf.isClosedUnderIsomorphisms
#check @CategoryTheory.HomotopyColimit.IsOf.diagramIsClosedUnderIsomorphisms
#check @CategoryTheory.ObjectProperty.prop_iff_of_iso
#check @CategoryTheory.ObjectProperty.prop_iff_of_isIso
