/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology

/-!
# Regularity for chosen twists on a projective spectrum

This leaf defines cohomological regularity for an explicit integral twist family. The
presentation API is a thin specialization to its actual twist family. The cohomological
bound is an input, so the same predicate applies to the canonical twists on standard
projective spaces without requiring the extra data of a universal twist presentation.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {A sigma : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
variable {calA : Nat -> sigma} [GradedRing calA]
variable [MonoidalCategory (Proj calA).Modules]

/-- A module is `m`-regular through degree `cohomologicalBound` for the supplied integral
twist family when its required positive-degree twisted cohomology vanishes. This is the
common predicate underlying presentation regularity and canonical projective-space regularity. -/
abbrev ProjTwistFamily.IsMRegular
    (P : ProjTwistFamily calA) (F : (Proj calA).Modules)
    (cohomologicalBound : Nat) (m : Int) : Prop :=
  ∀ i : Nat, 0 < i → i ≤ cohomologicalBound →
    IsZero
      (RingedSpace.moduleCohomology (X := (Proj calA).toRingedSpace)
        (P.tensorTwist F (m - i)) i)

namespace ProjTwistPresentation

/-- A module `F` is `m`-regular through cohomological degree `cohomologicalBound` with respect
to the actual twists recorded by `P`. This specializes `ProjTwistFamily.IsMRegular` to
`P.actualTwist`. -/
abbrev IsMRegular
    (P : ProjTwistPresentation calA) (F : (Proj calA).Modules)
    (cohomologicalBound : Nat) (m : Int) : Prop :=
  ProjTwistFamily.IsMRegular P.actualTwist F cohomologicalBound m

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

end ProjTwistPresentation

end AlgebraicGeometry
