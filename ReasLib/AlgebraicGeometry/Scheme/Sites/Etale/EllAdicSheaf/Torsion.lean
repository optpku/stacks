/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Rational
public import Mathlib.Algebra.Module.Torsion.Basic

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

section Stalk

variable {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- A geometric stalk of an integral ℓ-adic sheaf is torsion if and only if
it is annihilated by a single power of ℓ. -/
theorem stalk_isTorsion_iff (F : ZEllSheaf X ℓ) (x : GeometricPoint X) :
    Module.IsTorsion ℤ_[ℓ] (F.stalk x) ↔
      ∃ n : ℕ, Module.IsTorsionBy ℤ_[ℓ] (F.stalk x) (ℓ ^ n : ℤ_[ℓ]) := sorry

/-- Every geometric stalk of a torsion integral ℓ-adic sheaf is a torsion module. -/
theorem IsTorsion.stalk_isTorsion {F : ZEllSheaf X ℓ} (hF : F.IsTorsion)
    (x : GeometricPoint X) : Module.IsTorsion ℤ_[ℓ] (F.stalk x) := sorry

end Stalk

/-- On a Noetherian scheme, an integral ℓ-adic sheaf is torsion if and only if
every geometric stalk is a torsion ℓ-adic module. -/
theorem isTorsion_iff_forall_stalk_isTorsion
    {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (F : ZEllSheaf X ℓ) :
    F.IsTorsion ↔ ∀ x : GeometricPoint X, Module.IsTorsion ℤ_[ℓ] (F.stalk x) := sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
