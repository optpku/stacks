/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Affine base-change geometry for algebraization setups

The affine scheme, inverse-image open, and ideal-sheaf data induced by a ring map out of
the base ring of an affine algebraization setup.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (S : AffineAlgebraizationSetup A)
variable (A' : Type u) [CommRing A'] [Algebra A A']

/-- The affine scheme `Spec A'` obtained after changing the base ring from `A` to `A'`. -/
abbrev baseChangeSpec (S : AffineAlgebraizationSetup A) : Scheme :=
  Spec (CommRingCat.of A')

/-- The morphism `Spec A' ⟶ S.X` induced by the algebra map `A ⟶ A'`. -/
def baseChangeMap : S.baseChangeSpec A' ⟶ S.X :=
  Spec.map (CommRingCat.ofHom (algebraMap A A'))

/-- The inverse image of `S.U` in `Spec A'`. -/
def baseChangeOpen : (S.baseChangeSpec A').Opens :=
  S.baseChangeMap A' ⁻¹ᵁ S.U

/-- The morphism from the inverse-image open to `S.U` induced by base change. -/
def baseChangeOpenMap : (S.baseChangeOpen A').toScheme ⟶ S.U.toScheme :=
  (S.baseChangeMap A').resLE S.U (S.baseChangeOpen A') le_rfl

/-- The pullback to `Spec A'` of the ideal-sheaf datum associated to `S.I`. -/
noncomputable def baseChangeIdealSheaf : (S.baseChangeSpec A').IdealSheafData :=
  (Scheme.idealSheafDataOfIdealOnSpec S.I).comap (S.baseChangeMap A')

/-- The affine base-change map is definitionally induced by `algebraMap A A'`. -/
theorem baseChangeMap_def :
    S.baseChangeMap A' = Spec.map (CommRingCat.ofHom (algebraMap A A')) := sorry

/-- The base-changed open is the inverse image of `S.U`. -/
theorem baseChangeOpen_def :
    S.baseChangeOpen A' = S.baseChangeMap A' ⁻¹ᵁ S.U := sorry

/-- The restricted base-change map commutes with the two open immersions. -/
theorem baseChangeOpenMap_comp_ι :
    S.baseChangeOpenMap A' ≫ S.U.ι =
      (S.baseChangeOpen A').ι ≫ S.baseChangeMap A' := sorry

/-- Pulling the base-changed ideal back to the inverse-image open agrees with pulling the
original ideal on `S.U` back along the restricted base-change map. -/
theorem baseChangeIdealOnOpen_eq :
    (S.baseChangeIdealSheaf A').comap (S.baseChangeOpen A').ι =
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι).comap
        (S.baseChangeOpenMap A') := sorry

/-- A flat algebra structure makes the induced affine base-change map flat. -/
theorem baseChangeMap_flat [Module.Flat A A'] :
    Flat (S.baseChangeMap A') := sorry

/-- The map on the inverse-image open induced by a flat algebra is flat. -/
theorem baseChangeOpenMap_flat [Module.Flat A A'] :
    Flat (S.baseChangeOpenMap A') := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
