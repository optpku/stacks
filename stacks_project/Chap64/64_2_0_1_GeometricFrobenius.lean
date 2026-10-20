/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import ReasLib.FieldTheory.Finite.ArithmeticFrobenius
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Trace
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Characteristic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap59.«59_56_0_1»
public import stacks_project.Chap59.Definition_59_29_1_GeometricPoint
public import stacks_project.Chap64.Definition_64_3_4_GeometricFrobenius

public import ReasLib.AlgebraicGeometry.Scheme.Etale.FrobeniusStalk

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry MonoidalCategory

universe u

#check (AlgebraicGeometry.Scheme.Etale.geometricModuleStalk :
  ∀ {k : Type u} [Field k] {ℓ n : ℕ} {X : Scheme.{u}},
    Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))) →
    (Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ X) →
    ModuleCat.{u} (ZMod (ℓ ^ n)))

#check (AlgebraicGeometry.SchemeOverField.finiteFieldRank :
  (k : Type u) → [Field k] → [Fintype k] → (p : ℕ) → [Fact p.Prime] →
    [CharP k p] → [Algebra (ZMod p) k] → ℕ)
