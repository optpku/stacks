module

public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.QuotientLift
import StacksCheckRecall

/-!
@stack 00T0
-/

@[expose] public section

/- Lemma 10.136.18 (Tag 00T0): a syntomic quotient algebra admits a unit-ideal basic-open cover
whose localizations lift to relative global complete intersections.  The canonical owner is
`Algebra.Syntomic.exists_relativeGlobalCompleteIntersectionLiftCover_of_quotient`: its namespace
is determined by the syntomic hypothesis, and the owner's structured sub-APIs already separate
the lift, standard-open, and set-cover views.  The `Nonempty` equivalence is retained
because the source asserts existence rather than selecting a canonical lift. -/
@[stacks 00T0]
#check @Algebra.Syntomic.exists_relativeGlobalCompleteIntersectionLiftCover_of_quotient
