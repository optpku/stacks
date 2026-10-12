/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.EssentialFiniteness.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.54.1

This chapter entry is a source-facing recall of the neutral essential finite-presentation API.
The reusable owners live under `ReasLib.RingTheory.EssentialFiniteness`.

@stack 00QM
-/

/- Definition 10.54.1 (1): a ring homomorphism `R → S` is essentially of finite type when it is
the canonical mathlib notion `RingHom.EssFiniteType`. -/
@[stacks 00QM "(1)"]
#check @RingHom.EssFiniteType

/- Definition 10.54.1 (2): the canonical owner for an essentially finitely presented algebra is
`Algebra.EssFinitePresentation`; its ring-homomorphism form is `RingHom.EssFinitePresentation`. -/
@[stacks 00QM "(2)"]
#check @Algebra.EssFinitePresentation
@[stacks 00QM "(2), ring-hom formulation"]
#check @RingHom.EssFinitePresentation
