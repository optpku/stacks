module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness across a relative effective Cartier divisor

This file owns the criterion extending flatness from the complement of a relative effective
Cartier divisor to the whole source.

-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Scheme.Hom

variable {X S : Scheme.{u}}

namespace IsRelativeEffectiveCartierDivisor

/-- A morphism flat away from a relative effective Cartier divisor is flat everywhere. -/
@[stacks 062W]
theorem flat_of_flatAt_outside_support
    (f : X ⟶ S) (D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D]
    (hflat : ∀ x : X, x ∉ D.support → Scheme.Hom.flatAt f x) :
    Flat f := sorry

/-- The pointwise form of flatness supplied by the global criterion. -/
theorem flatAt_of_flatAt_outside_support
    (f : X ⟶ S) (D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D]
    (hflat : ∀ x : X, x ∉ D.support → Scheme.Hom.flatAt f x) (x : X) :
    Scheme.Hom.flatAt f x := by
  exact
    (Scheme.Hom.flat_iff_forall_flatAt f).1
      (IsRelativeEffectiveCartierDivisor.flat_of_flatAt_outside_support f D hflat) x

end IsRelativeEffectiveCartierDivisor

end AlgebraicGeometry
