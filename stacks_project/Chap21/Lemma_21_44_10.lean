module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect.InternalHom
import StacksCheckRecall

@[expose] public section

/- Lemma 21.44.10 (08JI): a termwise finite-free-retract complex bounded above computes
derived internal Hom into a bounded-below complex by the canonical internal-Hom complex. -/
@[stacks 08JI]
#check @RingedSite.CochainComplex.InternalHom.represents_of_bounds

#check @RingedSite.CochainComplex.InternalHom.represents_of_strictBounds
