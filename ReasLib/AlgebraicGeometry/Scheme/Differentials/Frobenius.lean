/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative

/-!
# Relative differentials of Frobenius

This leaf owns the canonical comparison from relative differentials over a base to relative
differentials over the relative Frobenius target. The construction uses the universal derivation
and relative-differentials API, so applications can reuse its section formula and theorem-level
isomorphism instance without rebuilding a derivation.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

section

variable {p : ℕ} [Fact p.Prime]
variable {X S : Scheme.{u}}
variable [Scheme.IsCharP S p]
variable (f : X ⟶ S)

/-- The universal differential on the relative-Frobenius target vanishes on sections pulled back
from `S`; this is the Frobenius-specific input to the generic comparison construction. -/
theorem relativeFrobeniusDifferential_d_app
    {U : X.Opensᵒᵖ}
    (a : ((TopCat.Sheaf.pullback CommRingCat f.base).obj S.sheaf).1.obj U) :
    (TopCat.Sheaf.relativeDifferential
      (RingedSpace.Hom.inverseImageStructureSheafHomComm
        (relativeFrobenius (p := p) f).toShHom)).d
        ((RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom).hom.app U a) = 0 := sorry

/-- The relative derivation defining the Frobenius differential comparison. -/
def relativeFrobeniusDifferentialDerivation :
    SheafOfModules.RelativeDerivation
      (J := Opens.grothendieckTopology X)
      (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom)
      (TopCat.Sheaf.relativeDifferentials
        (RingedSpace.Hom.inverseImageStructureSheafHomComm
          (relativeFrobenius (p := p) f).toShHom)) where
  d := (TopCat.Sheaf.relativeDifferential
    (RingedSpace.Hom.inverseImageStructureSheafHomComm
      (relativeFrobenius (p := p) f).toShHom)).d
  d_mul := (TopCat.Sheaf.relativeDifferential
    (RingedSpace.Hom.inverseImageStructureSheafHomComm
      (relativeFrobenius (p := p) f).toShHom)).d_mul
  d_map := (TopCat.Sheaf.relativeDifferential
    (RingedSpace.Hom.inverseImageStructureSheafHomComm
      (relativeFrobenius (p := p) f).toShHom)).d_map
  d_app := relativeFrobeniusDifferential_d_app (p := p) f

/-- The canonical map `Ω[f] ⟶ Ω[relativeFrobenius f]`. -/
@[stacks 0CCC]
noncomputable def relativeFrobeniusDifferentialComparison :
    TopCat.Sheaf.relativeDifferentials
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom) ⟶
      TopCat.Sheaf.relativeDifferentials
        (RingedSpace.Hom.inverseImageStructureSheafHomComm
          (relativeFrobenius (p := p) f).toShHom) :=
  TopCat.Sheaf.relativeDifferentialDesc
    (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom)
    (relativeFrobeniusDifferentialDerivation (p := p) f)

/-- The Frobenius differential comparison sends a universal differential to the target universal
differential sectionwise. -/
@[stacks 0CCC]
theorem relativeFrobeniusDifferentialComparisonSpec
    {U : X.Opensᵒᵖ} (t : X.presheaf.obj U) :
    (relativeFrobeniusDifferentialComparison (p := p) f).val.app U
        (((TopCat.Sheaf.relativeDifferential
          (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom)).app U).d t) =
      ((TopCat.Sheaf.relativeDifferential
        (RingedSpace.Hom.inverseImageStructureSheafHomComm
          (relativeFrobenius (p := p) f).toShHom)).app U).d t := sorry

/-- In characteristic `p`, the relative Frobenius differential comparison is an isomorphism. -/
@[stacks 0CCC, instance]
instance relativeFrobeniusDifferentialComparison_isIso :
    IsIso (relativeFrobeniusDifferentialComparison (p := p) f) := sorry

end

end AlgebraicGeometry.Scheme.Hom
