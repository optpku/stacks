/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Relative
import StacksCheckRecall

/-!
# Definition 15.81.2

@stack 05GZ
-/

@[expose] public section

universe u v w

/-! # Definition 15.81.2: relative finite presentation of modules -/

/- Definition 15.81.2, tag `05GZ`: the canonical relative finite-presentation owner. -/
@[stacks 05GZ "relative finite presentation of a module"]
#check fun (R : Type u) (A : Type v) (M : Type w)
    [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] ↦
  (Module.FinitePresentationRelativeTo R A M : Prop)

/- Explicit restriction-of-scalars predicate used by the owner. -/
#check @Module.FinitePresentationAlong

/- The owner forces finite type of the ambient algebra. -/
#check @Module.FinitePresentationRelativeTo.finiteType

/- The owner implies ordinary finite presentation over the ambient algebra. -/
#check @Module.FinitePresentationRelativeTo.finitePresentation
