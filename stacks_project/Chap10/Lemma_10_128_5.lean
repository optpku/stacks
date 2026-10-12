/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.Fiber.Regular
import StacksCheckRecall

/-!
# Regular Elements on the Closed Fiber

@stack 046Z
-/

@[expose] public section

/- Lemma 10.128.5: for a flat, essentially finitely presented local map `R → S`,
an element regular on
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` is regular in `S`, and its
principal quotient is flat over `R`. -/
@[stacks 046Z "closed-fiber quotient presentation"]
#check @RingHom.EssFinitePresentation.flat_quotient_and_isRegular_of_closedFiberQuotient

-- The reusable owner is stated on the canonical fiber and exposes both conclusions separately.
@[stacks 046Z "canonical closed-fiber form"]
#check @RingHom.EssFinitePresentation.flat_quotient_and_isRegular_of_closedFiber
@[stacks 046Z "(1), flat quotient clause"]
#check @RingHom.EssFinitePresentation.flat_quotient_of_closedFiber
@[stacks 046Z "(2), regular element clause"]
#check @RingHom.EssFinitePresentation.isRegular_of_closedFiber
