/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.ExternalTensorComplex

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
  (Limits.pullback a b).toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends
  (Limits.pullback a b).toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization
  (Limits.pullback a b).toRingedSpace]

variable (F : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ⥤
  RingedSpace.ModuleDerived.Perfect (X := Y.toRingedSpace))
variable (E G : ℕ → RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace))

/-- Each external tensor product term is perfect on the scheme fiber product. -/
theorem termPerfect (n : ℕ) :
    RingedSpace.ModuleDerived.IsPerfect
      (Kunneth.externalTensorProduct a b (E n).obj (F.obj (G n)).obj) := sorry

/-- The external tensor product of the indexed perfect derived objects in degree `n`. -/
noncomputable def term (n : ℕ) :
    RingedSpace.ModuleDerived.Perfect (X := (Limits.pullback a b).toRingedSpace) :=
  ⟨Kunneth.externalTensorProduct a b (E n).obj (F.obj (G n)).obj,
    termPerfect a b F E G n⟩

/-- The descending complex formed from explicit adjacent external tensor product differentials. -/
noncomputable def ofDifferentials
    (d : ∀ n, term a b F E G (n + 1) ⟶ term a b F E G n)
    (squareZero : ∀ n, d (n + 1) ≫ d n = 0) :
    ChainComplex (RingedSpace.ModuleDerived.Perfect
      (X := (Limits.pullback a b).toRingedSpace)) ℕ :=
  ChainComplex.of (term a b F E G) d squareZero

/-- The degree `n` object of the explicit external tensor product complex. -/
theorem ofDifferentials_X
    (d : ∀ n, term a b F E G (n + 1) ⟶ term a b F E G n)
    (squareZero : ∀ n, d (n + 1) ≫ d n = 0) (n : ℕ) :
    (ofDifferentials a b F E G d squareZero).X n = term a b F E G n := sorry

/-- The adjacent differential of the explicit external tensor product complex is the supplied map. -/
theorem ofDifferentials_d
    (d : ∀ n, term a b F E G (n + 1) ⟶ term a b F E G n)
    (squareZero : ∀ n, d (n + 1) ≫ d n = 0) (n : ℕ) :
    (ofDifferentials a b F E G d squareZero).d (n + 1) n = d n := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.ExternalTensorComplex
