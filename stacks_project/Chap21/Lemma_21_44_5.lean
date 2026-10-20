module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Free.LocalLift
import StacksCheckRecall

@[expose] public section

/- Lemma 21.44.5 (08FN): a morphism from a finite-free retract lifts locally through an
epimorphism. -/
@[stacks 08FN] #check @SheafOfModules.RingedSite.FiniteFreeRetract.exists_cover_lift
