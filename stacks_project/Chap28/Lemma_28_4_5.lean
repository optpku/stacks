module

public import ReasLib.RingTheory.CohenMacaulay.Local
public import ReasLib.RingTheory.LocalProperty.FiniteType
public import ReasLib.RingTheory.Regular.Local
import StacksCheckRecall

/-!
# Lemma 28.4.5 compatibility

The chapter's three locality assertions are now neutral commutative-algebra
instances. The finite-type case is grounded in mathlib's local
ring-homomorphism property `RingHom.finiteType_isLocal`.
-/

/- Lemma 28.4.5: the standard ring properties used in Chapter 28 are local. -/
@[expose] public section

universe u

/- Lemma 28.4.5 (1): the Cohen-Macaulay property is local. -/
@[stacks 01OT]
#check
  (CohenMacaulayRing.ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A))

/- Lemma 28.4.5 (2): the regular-ring property is local. -/
@[stacks 01OT]
#check
  (IsRegularRing.ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ IsRegularRing A))

/- Lemma 28.4.5 (3): being of finite type over `ℤ` is local. -/
@[stacks 01OT]
#check
  (Algebra.FiniteType.int_ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ Algebra.FiniteType ℤ A))
