/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology

/-!
# Regularity for chosen twists on a projective spectrum

This leaf gives the cohomological regularity predicate for a module together
with an explicitly chosen integral twist presentation.  The cohomological
bound is an input, so the API applies to standard projective spaces and to
other projective-spectrum presentations with a known bound.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjTwistPresentation

variable {A sigma : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
variable {calA : Nat -> sigma} [GradedRing calA]
variable [MonoidalCategory (Proj calA).Modules]

/-- A module `F` is `m`-regular through cohomological degree `cohomologicalBound` with respect
to the actual twists recorded by `P`. -/
abbrev IsMRegular
    (P : ProjTwistPresentation calA) (F : (Proj calA).Modules)
    (cohomologicalBound : Nat) (m : Int) : Prop :=
  ∀ i : Nat, 0 < i → i ≤ cohomologicalBound →
    IsZero
      (RingedSpace.moduleCohomology (X := (Proj calA).toRingedSpace)
        (P.tensorTwist F (m - i)) i)

/-- The cohomological vanishing formulation of `P.IsMRegular F cohomologicalBound m`. -/
theorem isMRegular_iff
    (P : ProjTwistPresentation calA) (F : (Proj calA).Modules)
    (cohomologicalBound : Nat) (m : Int) :
    P.IsMRegular F cohomologicalBound m ↔
      ∀ i : Nat, 0 < i → i ≤ cohomologicalBound →
        IsZero
          (RingedSpace.moduleCohomology (X := (Proj calA).toRingedSpace)
            (P.tensorTwist F (m - i)) i) := sorry

/-- Regularity through a given cohomological degree restricts to every smaller degree. -/
theorem IsMRegular.mono
    {P : ProjTwistPresentation calA} {F : (Proj calA).Modules}
    {cohomologicalBound cohomologicalBound' : Nat} {m : Int}
    (hF : P.IsMRegular F cohomologicalBound m)
    (hBound : cohomologicalBound' ≤ cohomologicalBound) :
    P.IsMRegular F cohomologicalBound' m := sorry

/-- An `m`-regular module has the required cohomology vanishing in every positive degree at most
its specified cohomological bound. -/
theorem isMRegular_isZero
    (P : ProjTwistPresentation calA) (F : (Proj calA).Modules)
    (cohomologicalBound : Nat) {m : Int}
    (hF : P.IsMRegular F cohomologicalBound m)
    {i : Nat} (hi : 0 < i) (hi_bound : i ≤ cohomologicalBound) :
    IsZero
      (RingedSpace.moduleCohomology (X := (Proj calA).toRingedSpace)
        (P.tensorTwist F (m - i)) i) := sorry

end AlgebraicGeometry.ProjTwistPresentation
