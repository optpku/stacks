/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.CommSq
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

/-!
# Dual-number points of schemes

This leaf owns the canonical morphisms in the dual-number square associated to
a scheme morphism at a point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DualNumber

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The closed-point morphism from `Spec κ(x)` to the dual-number spectrum
`Spec κ(x)[ε]`, induced contravariantly by the projection `κ(x)[ε] → κ(x)`. -/
noncomputable def dualNumberPointInclusion {X : Scheme.{u}} (x : X) :
    Spec (CommRingCat.of (X.residueField x)) ⟶
      Spec (CommRingCat.of ((X.residueField x)[ε])) :=
  Spec.map
    (CommRingCat.ofHom
      ((TrivSqZeroExt.fstHom (S := X.residueField x) (R := X.residueField x)
        (M := X.residueField x)).toRingHom))

/-- The morphism from `Spec κ(x)[ε]` to `Spec κ(f(x))` induced by the canonical
algebra map `κ(f(x)) → κ(x)[ε]`. -/
noncomputable def dualNumberToBasePoint {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec (CommRingCat.of ((X.residueField x)[ε])) ⟶
      Spec (CommRingCat.of (S.residueField (f x))) :=
  Spec.map
    (CommRingCat.ofHom
      (algebraMap (S.residueField (f x)) ((X.residueField x)[ε])))

/-- The composite through the dual-number spectrum is the spectrum map induced
by the residue-field homomorphism. -/
theorem dualNumberPointInclusion_comp_toBasePoint
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    dualNumberPointInclusion x ≫ dualNumberToBasePoint f x =
      Spec.map (f.residueFieldMap x) := by
  unfold dualNumberPointInclusion dualNumberToBasePoint
  rw [← Spec.map_comp]
  rfl

/-- The canonical residue-field point maps and dual-number maps form a
commutative square over a scheme morphism. -/
@[stacks 0B2A]
theorem dualNumberPointCommSq {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    CommSq (X.fromSpecResidueField x) (dualNumberPointInclusion x) f
      (dualNumberToBasePoint f x ≫ S.fromSpecResidueField (f x)) := by
  constructor
  rw [← Category.assoc, dualNumberPointInclusion_comp_toBasePoint]
  exact (f.SpecMap_residueFieldMap_fromSpecResidueField x).symm

/-- The residue-field morphism `κ(f(x))[ε] ⟶ κ(x)[ε]` transports both dual-number
coefficients through the canonical residue-field map. -/
noncomputable def dualNumberResidueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    CommRingCat.of ((Y.residueField (f x))[ε]) ⟶
      CommRingCat.of ((X.residueField x)[ε]) :=
  CommRingCat.ofHom
    { toFun := fun z ↦
        ⟨(f.residueFieldMap x).hom z.fst, (f.residueFieldMap x).hom z.snd⟩
      map_one' := by
        apply TrivSqZeroExt.ext <;> simp
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext <;> simp
      map_zero' := by
        apply TrivSqZeroExt.ext <;> simp
      map_add' := by
        intro a b
        apply TrivSqZeroExt.ext <;> simp }

/-- Applying `dualNumberResidueFieldMap` transports the two dual-number
coefficients coefficientwise. -/
theorem dualNumberResidueFieldMap_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (z : (Y.residueField (f x))[ε]) :
    dualNumberResidueFieldMap f x z =
      ⟨(f.residueFieldMap x).hom z.fst, (f.residueFieldMap x).hom z.snd⟩ := rfl

end AlgebraicGeometry.Scheme.Hom
