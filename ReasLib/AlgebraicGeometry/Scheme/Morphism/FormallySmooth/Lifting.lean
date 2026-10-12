/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import Mathlib.CategoryTheory.LiftingProperties.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallySmooth

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Formal smoothness is equivalent to the lifting property against every affine
first-order thickening of schemes. -/
theorem iff_hasLiftingProperty :
    FormallySmooth f ↔
      ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
        [IsFirstOrderThickening i], HasLiftingProperty i f := sorry

/-- A formally smooth morphism has the lifting property against every affine first-order
thickening. -/
instance hasLiftingProperty [FormallySmooth f] {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (i : T ⟶ T') [IsFirstOrderThickening i] : HasLiftingProperty i f := sorry

/-- The affine first-order-thickening lifting property implies formal smoothness. -/
theorem of_hasLiftingProperty
    (h_lift : ∀ {T T' : Scheme.{u}} [IsAffine T] [IsAffine T'] (i : T ⟶ T')
      [IsFirstOrderThickening i], HasLiftingProperty i f) : FormallySmooth f := sorry

end AlgebraicGeometry.FormallySmooth
