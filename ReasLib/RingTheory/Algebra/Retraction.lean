module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Retract
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.AlgHom.ULift

@[expose] public section

/-!
# Retract extensions of commutative algebras

A retract extension bundles the intermediate algebra and its retraction.
The categorical bridge uses universe lifts only at the `CommRingCat`
boundary; map-facing consumers work with the original rings.
-/

open CategoryTheory

universe u v w

namespace Algebra

/-- An `A`-algebra over `R` equipped with an `A`-algebra retraction back to
`A`. -/
@[stacks 07CE "retract extension of an algebra"]
structure RetractExtension (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] where
  /-- The carrier of the retract extension. -/
  carrier : Type w
  /-- The carrier is a commutative ring. -/
  [instCommRing : CommRing carrier]
  /-- The carrier is an algebra over the base ring. -/
  [instAlgebraBase : Algebra R carrier]
  /-- The carrier is an algebra over the source algebra. -/
  [instAlgebraSource : Algebra A carrier]
  /-- The two algebra structures form the expected scalar tower. -/
  [instScalarTower : IsScalarTower R A carrier]
  /-- The retraction to the source algebra. -/
  retraction : carrier →ₐ[A] A

attribute [instance] RetractExtension.instCommRing
  RetractExtension.instAlgebraBase RetractExtension.instAlgebraSource
  RetractExtension.instScalarTower

namespace RetractExtension

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Build a retract extension from an algebra retraction.  The carrier and its
algebra structures are inferred from the retraction and the ambient instances. -/
@[stacks 07CE "retract extension constructor"]
def of {B : Type w} [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (retraction : B →ₐ[A] A) :
    RetractExtension.{u, v, w} R A where
  carrier := B
  instCommRing := inferInstance
  instAlgebraBase := inferInstance
  instAlgebraSource := inferInstance
  instScalarTower := inferInstance
  retraction := retraction

/-- The carrier supplied to `RetractExtension.of` is recovered by projection. -/
@[simp]
theorem carrier_of {B : Type w} [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (retraction : B →ₐ[A] A) :
    (of (R := R) (A := A) retraction).carrier = B := sorry

/-- The retraction supplied to `RetractExtension.of` is recovered by projection. -/
@[simp]
theorem retraction_of {B : Type w} [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (retraction : B →ₐ[A] A) :
    (of (R := R) (A := A) retraction).retraction = retraction := sorry

/-- An algebra retraction is automatically a left inverse to its source
algebra map. -/
@[stacks 07CE "algebra retraction equation", simp]
theorem retract (E : RetractExtension.{u, v, w} R A) :
    E.retraction.toRingHom.comp (algebraMap A E.carrier) = RingHom.id A := sorry

/-- Pointwise form of the retraction law. -/
@[stacks 07CE "retraction on the source algebra", simp]
theorem retraction_algebraMap (E : RetractExtension.{u, v, w} R A) (a : A) :
    E.retraction (algebraMap A E.carrier a) = a := sorry

/-- The categorical retraction equation in commutative `A`-algebras after
lifting both algebras to a common universe. -/
@[stacks 07CE "categorical algebra retraction equation"]
theorem toAlgRetract_retract (E : RetractExtension.{u, v, w} R A) :
    CommAlgCat.ofHom (IsScalarTower.toAlgHom A A E.carrier).uliftMap ≫
      CommAlgCat.ofHom E.retraction.uliftMap =
      𝟙 (CommAlgCat.of A (ULift.{max v w} A)) := sorry

/-- The retract extension as a categorical retract of commutative
`A`-algebras. -/
@[stacks 07CE "categorical algebra retract extension"]
noncomputable def toAlgRetract (E : RetractExtension.{u, v, w} R A) :
    CategoryTheory.Retract
      (CommAlgCat.of A (ULift.{max v w} A))
      (CommAlgCat.of A (ULift.{v} E.carrier)) where
  i := CommAlgCat.ofHom (IsScalarTower.toAlgHom A A E.carrier).uliftMap
  r := CommAlgCat.ofHom E.retraction.uliftMap
  retract := E.toAlgRetract_retract

/-- The underlying categorical retract of commutative rings. -/
@[stacks 07CE "underlying categorical ring retract extension"]
noncomputable def toRingRetract (E : RetractExtension.{u, v, w} R A) :
    CategoryTheory.Retract
      (CommRingCat.of (ULift.{max v w} A))
      (CommRingCat.of (ULift.{v} E.carrier)) :=
  E.toAlgRetract.map (forget₂ (CommAlgCat A) CommRingCat)

end RetractExtension

end Algebra
