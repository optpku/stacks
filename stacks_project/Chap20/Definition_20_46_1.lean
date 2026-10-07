module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
import StacksCheckRecall

@[expose] public section

/-!
# Definition 20.46.1

Strict perfectness is owned by the generic bounded-termwise object property for complexes of
modules over a sheaf of rings.  No ringed-space-specific alias is needed.
-/

/- Definition 20.46.1 (08C4): a strictly perfect complex is bounded and termwise a retract of a
finite free module sheaf. -/
@[stacks 08C4] #check @SheafOfModules.CochainComplex.strictlyPerfect

#check @SheafOfModules.CochainComplex.IsStrictlyPerfect
#check @SheafOfModules.CochainComplex.StrictlyPerfect
#check @SheafOfModules.CochainComplex.isStrictlyPerfect_iff_explicit
#check @SheafOfModules.CochainComplex.IsStrictlyPerfect.bounded
#check @SheafOfModules.CochainComplex.IsStrictlyPerfect.term_retract_free

end
