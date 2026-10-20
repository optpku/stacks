module

public import ReasLib.CategoryTheory.Sites.Presheaf.GlobalSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v w

variable {C : Type u} [Category.{v} C] (F : Presheaf C)

/- Definition 7.45.1: the global sections of a presheaf of sets F on a site C
(which need not have a final object) is the set Γ(C, F) = Mor_PSh(C)(*, F),
where * is the final object of PSh(C), i.e., the singleton-valued presheaf.
The reusable definition is exactly the Hom type from Presheaf.terminal C. -/
@[stacks 06UN] #check (CategoryTheory.Presheaf.globalSections F : Type (max u w))

#check (CategoryTheory.Presheaf.terminalIsTerminal.{w} C :
  IsTerminal (CategoryTheory.Presheaf.terminal.{w} C))
