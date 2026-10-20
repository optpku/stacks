module

public import ReasLib.RingTheory.Regular.Field
public import ReasLib.RingTheory.Regular.Identity
import StacksCheckRecall

/-!
# Definition 15.41.1

@stack 07BZ

This file recalls the shared definition and its canonical fiber API.
-/

@[expose] public section

/- Definition 15.41.1: a ring map is regular when it is flat and all of its
residue-field fibers are geometrically regular. -/
@[stacks 07BZ] #check @RingHom.Regular

#check @RingHom.Regular.iff_flat_and_geometricallyRegular_fiber
#check @RingHom.Regular.isRegularRing_fiber
#check @RingHom.Regular.isReduced_fiber
#check @RingHom.Regular.instId
#check @RingHom.Regular.instAlgebraMap
#check @Algebra.isGeometricallyRegular_of_algEquiv
