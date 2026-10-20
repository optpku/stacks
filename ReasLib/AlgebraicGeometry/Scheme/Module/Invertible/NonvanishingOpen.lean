/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingOpen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Power
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Nonvanishing opens of sections of invertible modules on schemes

This file relates nonvanishing opens of sections of invertible scheme modules to the
corresponding stalkwise constructions on the underlying ringed space.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

namespace Invertible

/-- The nonvanishing open of a global section of a positive tensor power of an invertible module.
Its carrier is the actual stalkwise nonvanishing locus, rather than the top open. -/
@[stacks 01PS "positive tensor-power nonvanishing open"]
noncomputable def nonvanishingOpen {L : X.Modules}
    (hL : Invertible L) {n : ℕ}
    (s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤)) : X.Opens :=
  @RingedSpace.sectionNonvanishingOpen X.toRingedSpace _
    (RingedSpace.TensorPower.sheaf L n)
    (ringedSpaceIsInvertible (tensorPower_isInvertible hL n))
    (RingedSpace.sectionFromTop (RingedSpace.TensorPower.sheaf L n) s)

/-- The carrier of the tensor-power nonvanishing open is the corresponding stalkwise
nonvanishing locus. -/
@[simp]
theorem coe_nonvanishingOpen {L : X.Modules}
    (hL : Invertible L) {n : ℕ}
    (s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤)) :
    (hL.nonvanishingOpen s : Set X) =
      RingedSpace.sectionNonvanishingLocus X.toRingedSpace
        (RingedSpace.TensorPower.sheaf L n)
        (RingedSpace.sectionFromTop (RingedSpace.TensorPower.sheaf L n) s) := sorry

/-- On a tensor-power nonvanishing open, the defining section trivializes the corresponding
tensor power. -/
theorem isIso_sectionOverHom_nonvanishingOpen {L : X.Modules} [hL : Invertible L]
    {n : ℕ} (s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤)) :
    IsIso
      (RingedSpace.sectionOverHom X.toRingedSpace (RingedSpace.TensorPower.sheaf L n)
        (RingedSpace.sectionFromTop (RingedSpace.TensorPower.sheaf L n) s)
        (hL.nonvanishingOpen s)) := sorry

/-- The nonvanishing open of a global section of an invertible module. -/
@[stacks 01PS "degree-one nonvanishing open"]
noncomputable def sectionNonvanishingOpen {L : X.Modules}
    (hL : Invertible L)
    (s : Γ(L, ⊤)) : X.Opens :=
  @RingedSpace.sectionNonvanishingOpen X.toRingedSpace _ L
    (ringedSpaceIsInvertible hL) (RingedSpace.sectionFromTop L s)

/-- The carrier of the degree-one nonvanishing open is the corresponding stalkwise
nonvanishing locus. -/
@[simp]
theorem coe_sectionNonvanishingOpen {L : X.Modules}
    (hL : Invertible L)
    (s : Γ(L, ⊤)) :
    (hL.sectionNonvanishingOpen s : Set X) =
      RingedSpace.sectionNonvanishingLocus X.toRingedSpace L
        (RingedSpace.sectionFromTop L s) := sorry

/-- On a degree-one nonvanishing open, the defining section trivializes the invertible module. -/
instance isIso_sectionOverHom_sectionNonvanishingOpen {L : X.Modules} [hL : Invertible L]
    (s : Γ(L, ⊤)) :
    IsIso
      (RingedSpace.sectionOverHom X.toRingedSpace L
        (RingedSpace.sectionFromTop L s) (hL.sectionNonvanishingOpen s)) := sorry

end Invertible

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.IsAffineOpen

/-- The intersection of an affine open with the nonvanishing open of a global section of an
invertible module is affine. -/
theorem inf_sectionNonvanishingOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (L : X.Modules)
    [hL : Scheme.Modules.Invertible L] (s : Γ(L, ⊤)) :
    IsAffineOpen (U ⊓ hL.sectionNonvanishingOpen s) := sorry

end AlgebraicGeometry.IsAffineOpen

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The inclusion of the nonvanishing open of a global section of an invertible module is an
affine morphism. -/
instance isAffineHom_ι_sectionNonvanishingOpen {X : Scheme.{u}} {L : X.Modules}
    [hL : Invertible L] (s : Γ(L, ⊤)) :
    IsAffineHom (hL.sectionNonvanishingOpen s).ι := sorry

end AlgebraicGeometry.Scheme.Modules.Invertible
