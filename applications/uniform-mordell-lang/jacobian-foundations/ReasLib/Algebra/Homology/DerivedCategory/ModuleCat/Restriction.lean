module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat

@[expose] public section

/-!
# Derived restriction of scalars

Restriction of scalars is exact for modules over commutative rings.  This file records the induced
functor on unbounded derived categories at the lowest reusable `ModuleCat` layer, using Mathlib's
proved exactness instances rather than selecting data through a deferred proof.
@stack 091W
-/

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

namespace DerivedRestriction

/-- Restriction of scalars, bundled with its canonical exactness. -/
@[stacks 03B8 "exact restriction of scalars for modules"]
noncomputable abbrev exact (σ : R →+* S) :
    ModuleCat.{max u v, u} S ⥤ₑ ModuleCat.{max u v, u} R :=
  ExactFunctor.of (ModuleCat.restrictScalars.{max u v} σ)

end DerivedRestriction

/-- The derived restriction-of-scalars functor along an explicit commutative-ring homomorphism. -/
@[stacks 0BYX "derived restriction of scalars for modules"]
noncomputable abbrev derivedRestrictionOfScalars (σ : R →+* S) :
    DerivedCategory (ModuleCat.{max u v, u} S) ⥤ DerivedCategory (ModuleCat.{max u v, u} R) :=
  (ModuleCat.restrictScalars.{max u v} σ).mapDerivedCategory

namespace DerivedRestriction

/-- A scalar killed by `σ` acts by zero after derived restriction of scalars along `σ`. -/
@[stacks 091W "scalar annihilation after derived restriction"]
theorem smul_id_obj_eq_zero {A B : Type u} [CommRing A] [CommRing B]
    (σ : A →+* B) (K : DerivedCategory (ModuleCat.{max u v, u} B))
    {r : A} (hr : σ r = 0) :
    r • 𝟙 ((derivedRestrictionOfScalars σ).obj K) = 0 := sorry

end DerivedRestriction

end CategoryTheory.ModuleCat
