/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.CategoryTheory.Adjunction.Abelian

/-!
# Injective objects under change of rings

Coextension of scalars sends injective modules to injective modules. For a commutative ring map,
preservation of injective modules by restriction of scalars is equivalent both to exactness of the
tensor left adjoint and to flatness of the ring map.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

namespace CoextendScalars

variable {R S : Type u} [Ring R] [Ring S]

/-- Coextension of scalars along a ring homomorphism sends injective modules to injective
modules. -/
instance injective (f : R →+* S) (E : ModuleCat.{max u v} R) [Injective E] :
    Injective ((ModuleCat.coextendScalars f).obj E) := sorry

end CoextendScalars

variable {R S : Type u} [CommRing R] [CommRing S]

namespace RestrictScalars

/-- Restriction of scalars preserves injective objects exactly when its tensor left adjoint is
exact. -/
theorem preservesInjectiveObjects_iff_extendScalars_exact (f : R →+* S) :
    (restrictScalars.{u} f).PreservesInjectiveObjects ↔
      exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
        (extendScalars.{u, u, u} f) := sorry

/-- Restriction of scalars preserves injective objects exactly for flat commutative
ring maps. -/
@[stacks 03B8]
theorem preservesInjectiveObjects_iff_flat (f : R →+* S) :
    (restrictScalars.{u} f).PreservesInjectiveObjects ↔ f.Flat := sorry

/-- Restriction of scalars along a flat commutative ring map preserves injective objects. -/
theorem preservesInjectiveObjects_of_flat
    (f : R →+* S) (h_flat : f.Flat) :
    (restrictScalars.{u} f).PreservesInjectiveObjects := sorry

/-- A non-flat commutative ring map gives a restriction-of-scalars functor that does not preserve
injective objects. -/
theorem not_preservesInjectiveObjects_of_not_flat
    (f : R →+* S) (h_flat : ¬ f.Flat) :
    ¬ (restrictScalars.{u} f).PreservesInjectiveObjects := sorry

end RestrictScalars

end ModuleCat
