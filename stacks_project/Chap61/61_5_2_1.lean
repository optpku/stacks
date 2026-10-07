module

public import ReasLib.Algebra.WLocalHull.Stage
import StacksCheckRecall

@[expose] public section

universe u

/- 61.5.2.1: for a ring `A` and a finite subset `E ⊆ A`, the finite-stage
algebra is `Algebra.WLocalHull.stage A E`, the product of specializing
localizations `specializingLocalization A p.elem p.span` over vanishing
patterns `p : Pattern A E` encoding decompositions `E = E' ⨿ E''` by
`E' = p.1` and `E'' = E \ p.1`. -/
@[stacks 096Z] #check (Algebra.WLocalHull.stage :
  ∀ (A : Type u) [CommRing A], Finset A → Type u)

#check Algebra.WLocalHull.specializingLocalization
#check Algebra.WLocalHull.Pattern.elem
#check Algebra.WLocalHull.Pattern.span
#check Algebra.WLocalHull.stage.eval
