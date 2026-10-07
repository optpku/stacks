module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.RingTheory.FormalFiber.FieldProperty.Basic
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import ReasLib.RingTheory.Regular.RingMap

@[expose] public section

/-!
# Permanence Laws for Field-Algebra Properties

The five laws are independent typeclasses so reusable arguments can require
exactly the permanence principles they use.  `FormalFiberLaws` is the bundled
convenience interface for results needing all five.

@stack 0BIR
-/

open IsLocalRing
open scoped TensorProduct

universe u v

namespace FieldAlgebraProperty

/-- The property is preserved by extending the ground field along an
essentially finite type field extension. -/
@[stacks 0BIR "finite-type ground-field base change"]
class EssFiniteTypeBaseChange
    (P : FieldAlgebraProperty.{u, max u v}) : Prop where
  /-- Base change along an essentially finite type extension of fields
  preserves the property. -/
  baseChange (k K : Type u) (A : Type (max u v))
      [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A]
      [IsNoetherianRing A] [Algebra.EssFiniteType k K] (hA : P k A) :
      P K (TensorProduct k K A)

/-- The property of Noetherian algebras can be checked on all prime
localizations. -/
@[stacks 0BIR "prime-local field-algebra property"]
class IsLocal (P : FieldAlgebraProperty.{u, v}) : Prop where
  /-- A Noetherian algebra has the property exactly when all its prime
  localizations have it. -/
  localizationCriterion (k : Type u) (A : Type v)
      [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A] :
      P k A ↔ ∀ p : PrimeSpectrum A, P k (Localization.AtPrime p.asIdeal)

/-- The property ascends on fibers through a regular second map after a flat
first map. -/
@[stacks 0BIR "regular ascent of a fiber property"]
class RegularFiberAscent (P : FieldAlgebraProperty.{u, u}) : Prop where
  /-- If `A → B` is flat, `B → C` is regular, and the fiber of `A → B` at
  `q` has the property, then the fiber of `A → C` at `q` has it. -/
  regularAscent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [(algebraMap B C).Regular]
      (q : PrimeSpectrum A)
      (hB : P q.asIdeal.ResidueField (q.asIdeal.Fiber B)) :
      P q.asIdeal.ResidueField (q.asIdeal.Fiber C)

/-- The property descends on closed fibers through a faithfully flat local
second map. -/
@[stacks 0BIR "faithfully flat descent of a closed-fiber property"]
class FaithfullyFlatDescent (P : FieldAlgebraProperty.{u, u}) : Prop where
  /-- For local maps `A → B → C`, faithfully flat descent along `B → C`
  carries the property from the closed fiber of `A → C` to that of
  `A → B`. -/
  closedFiberDescent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
      [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
      (hBC : RingHom.FaithfullyFlat (algebraMap B C))
      (hC : P (ResidueField A) ((maximalIdeal A).Fiber C)) :
      P (ResidueField A) ((maximalIdeal A).Fiber B)

/-- The property is preserved when the displayed ground field is enlarged by
a separable algebraic extension without changing the algebra. -/
@[stacks 0BIR "separable extension of the ground field"]
class SeparableExtension (P : FieldAlgebraProperty.{u, v}) : Prop where
  /-- Reinterpreting the same algebra over a separable algebraic extension of
  the ground field preserves the property. -/
  separableBaseChange (k k' : Type u) (A : Type v)
      [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k' A]
      [Algebra k A] [IsScalarTower k k' A] [Algebra.IsSeparable k k']
      (hA : P k A) : P k' A

/-- The complete collection of permanence laws used by the formal-fiber
machine.  Each law remains independently available for theorems that need
only part of the package. -/
@[stacks 0BIR "formal-fiber permanence laws"]
class FormalFiberLaws (P : FieldAlgebraProperty.{u, u}) : Prop
    extends P.EssFiniteTypeBaseChange, P.IsLocal, P.RegularFiberAscent,
      P.FaithfullyFlatDescent, P.SeparableExtension

/-- The five independent permanence principles bundled by `FormalFiberLaws`. -/
@[stacks 0BIR "formal-fiber permanence laws specification"]
theorem FormalFiberLaws.spec (P : FieldAlgebraProperty.{u, u}) [P.FormalFiberLaws] :
    P.EssFiniteTypeBaseChange ∧ P.IsLocal ∧ P.RegularFiberAscent ∧
      P.FaithfullyFlatDescent ∧ P.SeparableExtension := sorry

end FieldAlgebraProperty
