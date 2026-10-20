module

public import ReasLib.RingTheory.Smooth.AtPrime.Lifting
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.141.2 (Stacks tag `02HT`): let `R → S` be a Noetherian
finite-type ring map and let `q` be a prime of `S`.  Smoothness at `q` is
equivalent to the local lifting criterion for square-zero extensions, to the
same criterion for small extensions, and to the latter criterion restricted
to extensions inducing a bijection on residue fields.  The reusable owner
uses explicit `R`-algebra maps for the extension and the canonical target
closed point, so the source wording is represented without an accidental
`IsLocalHom` assumption on `R`.

@stack 02HT
-/
@[stacks 02HT]
#check @Algebra.IsSmoothAt.lifting_tfae

/- The atomic views and implication bridges are exposed by the shared owner. -/
#check @Algebra.IsSmoothAt.SquareZeroLifts
#check @Algebra.IsSmoothAt.SmallExtensionLifts
#check @Algebra.IsSmoothAt.SmallExtensionLifts.withResidue
#check @Algebra.IsSmoothAt.hasSquareZeroLifts
#check @AlgHom.toLiftingSquare
#check @AlgHom.HasLift.toRingSquare
#check @Algebra.IsSmoothAt.iff_hasSquareZeroLifts
#check @Algebra.IsSmoothAt.SquareZeroLifts.iff_smallExtensionLifts
#check @Algebra.IsSmoothAt.SmallExtensionLifts.iff_withResidue
#check @Algebra.IsSmoothAt.SquareZeroLifts.toSmallExtension
#check @Algebra.IsSmoothAt.SmallExtensionLifts.toWithResidue
#check @Algebra.IsSmoothAt.of_withResidue
