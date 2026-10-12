/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.LiftingProperties.Basic
import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Affine

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsClosedImmersion

/-- A morphism between affine schemes is a closed immersion exactly when it has the right
lifting property against every spectrum morphism induced by an injective commutative-ring
morphism. -/
theorem iff_hasLiftingProperty_spec_injective {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) :
    IsClosedImmersion f ↔
      ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B), Function.Injective φ →
        HasLiftingProperty (Spec.map φ) f := sorry

/-- A quasi-compact morphism of schemes is a closed immersion exactly when it has the
right lifting property against every spectrum morphism induced by an injective
commutative-ring morphism. -/
theorem iff_hasLiftingProperty_spec_injective_of_quasiCompact {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] :
    IsClosedImmersion f ↔
      ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B), Function.Injective φ →
        HasLiftingProperty (Spec.map φ) f := sorry

end AlgebraicGeometry.IsClosedImmersion
