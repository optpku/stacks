module

public import Mathlib.RingTheory.FinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.6.1

@stack 00F3
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.6.1 (1): a ring map `R → S` is of finite type exactly in the canonical sense of
`RingHom.FiniteType`; equivalently, for an `R`-algebra `S`, this is the algebra-map notion
`Algebra.FiniteType R S`. -/
@[stacks 00F3 "finite-type ring maps"]
#check @RingHom.FiniteType

/- Companion recall: for an `R`-algebra `S`, the finite-type condition on `algebraMap R S` is
equivalent to the owner typeclass `Algebra.FiniteType R S`. -/
@[stacks 00F3 "finite-type algebra bridge"]
#check @RingHom.finiteType_algebraMap

/- Definition 10.6.1 (2): a ring map `R → S` is of finite presentation exactly in the canonical
sense of `RingHom.FinitePresentation`; equivalently, for an `R`-algebra `S`, this is the
algebra-map notion `Algebra.FinitePresentation R S`. -/
@[stacks 00F3 "finite-presentation ring maps"]
#check @RingHom.FinitePresentation

/- Companion recall: for an `R`-algebra `S`, the finite-presentation condition on `algebraMap R S`
is equivalent to the owner typeclass `Algebra.FinitePresentation R S`. -/
@[stacks 00F3 "finite-presentation algebra bridge"]
#check @RingHom.finitePresentation_algebraMap
