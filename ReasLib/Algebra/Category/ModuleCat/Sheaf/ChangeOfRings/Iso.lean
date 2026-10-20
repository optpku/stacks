/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Scalar extension along an isomorphism of ring sheaves

Reverse restriction of scalars is a concrete left adjoint. Comparing it with the
chosen scalar-extension adjoint gives a reverse map for the chosen unit.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R S : Sheaf J RingCat.{w}}

variable (e : R ≅ S) [(restrictScalars.{z} e.hom).IsRightAdjoint]

/-- The inverse of the chosen scalar-extension unit, obtained by the explicit
reverse scalar restriction and the canonical comparison of left adjoints. -/
def extendRestrictUnitInv (M : SheafOfModules.{z} R) :
    (restrictScalars e.hom).obj ((extendScalars e.hom).obj M) ⟶ M :=
  (restrictScalars e.hom).map
      ((extendScalarsIso e.hom (restrictScalarsEquivalence e).toAdjunction).inv.app M) ≫
    (restrictScalarsRoundTrip e M).inv

/-- The scalar-extension unit with its specified inverse along an actual ring
isomorphism. The forward map is the original chosen adjunction unit. -/
def extendRestrictUnitIso (M : SheafOfModules.{z} R) :
    M ≅ (restrictScalars e.hom).obj ((extendScalars e.hom).obj M) where
  hom := (extendRestrictAdjunction e.hom).unit.app M
  inv := extendRestrictUnitInv e M
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The displayed unit isomorphism retains the original unit. -/
@[simp]
theorem extendRestrictUnitIso_hom (M : SheafOfModules.{z} R) :
    (extendRestrictUnitIso e M).hom = (extendRestrictAdjunction e.hom).unit.app M := rfl

/-- Its inverse is the specified restriction-of-scalars comparison. -/
@[simp]
theorem extendRestrictUnitIso_inv (M : SheafOfModules.{z} R) :
    (extendRestrictUnitIso e M).inv = extendRestrictUnitInv e M := rfl

end SheafOfModules.ChangeOfRings
