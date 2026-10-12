/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

/-!
# Algebraic properties of universal homeomorphisms

This leaf records the algebraic and pointwise characterization of universal
homeomorphisms of schemes.  The individual consequences are available as
theorems and as typeclass instances, so they can be used directly by APIs for
integral, universally injective, and surjective morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace UniversalHomeomorphism

variable {X Y : Scheme.{u}}

/-- A universal homeomorphism of schemes is integral. -/
@[stacks 04DF]
theorem isIntegralHom (f : X ⟶ Y) [UniversalHomeomorphism f] :
    IsIntegralHom f := sorry

/-- Universal homeomorphisms are integral morphisms for typeclass search. -/
instance instIsIntegralHom (f : X ⟶ Y) [UniversalHomeomorphism f] :
    IsIntegralHom f :=
  isIntegralHom f

/-- A universal homeomorphism of schemes is universally injective. -/
@[stacks 04DF]
theorem universallyInjective (f : X ⟶ Y) [UniversalHomeomorphism f] :
    UniversallyInjective f := sorry

/-- Universal homeomorphisms are universally injective for typeclass search. -/
instance instUniversallyInjective (f : X ⟶ Y) [UniversalHomeomorphism f] :
    UniversallyInjective f :=
  universallyInjective f

/-- A universal homeomorphism of schemes is surjective. -/
@[stacks 04DF]
theorem surjective (f : X ⟶ Y) [UniversalHomeomorphism f] :
    Surjective f := sorry

/-- Universal homeomorphisms are surjective for typeclass search. -/
instance instSurjective (f : X ⟶ Y) [UniversalHomeomorphism f] :
    Surjective f :=
  surjective f

/-- An integral, universally injective, and surjective morphism of schemes is a universal
homeomorphism. -/
@[stacks 04DF]
theorem of_isIntegralHom_of_universallyInjective_of_surjective
    (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] [Surjective f] :
    UniversalHomeomorphism f := sorry

/-- A morphism of schemes is a universal homeomorphism if and only if it is integral,
universally injective, and surjective. -/
@[stacks 04DF]
theorem iff_isIntegralHom_and_universallyInjective_and_surjective (f : X ⟶ Y) :
    UniversalHomeomorphism f ↔
      IsIntegralHom f ∧ UniversallyInjective f ∧ Surjective f := sorry

end UniversalHomeomorphism

end AlgebraicGeometry
