/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Torsion

/-!
# Torsion of canonical constructible ℓ-adic sheaves

The shared owners provide stagewise constructibility, adicity of the constant
sheaf, and torsion criteria for geometric inverse-limit stalks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.IsConstructible :
  ZEllSheaf X ℓ → Prop)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.constructible :
  ∀ F : ZEllSheaf X ℓ, F.IsConstructible)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.isAdic (constant X ℓ) :
  ∀ n : ℕ,
    IsIso (cokernel.desc ((ℓ ^ (n + 1)) • 𝟙 ((constant X ℓ).stage (n + 1)))
      ((constant X ℓ).stepMap n) ((constant X ℓ).step_comp_nsmul n)))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalk_isTorsion_iff :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    Module.IsTorsion ℤ_[ℓ] (F.stalk x) ↔
      ∃ n : ℕ, Module.IsTorsionBy ℤ_[ℓ] (F.stalk x) (ℓ ^ n : ℤ_[ℓ]))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.IsTorsion.stalk_isTorsion :
  ∀ {F : ZEllSheaf X ℓ}, F.IsTorsion →
    ∀ x : GeometricPoint X, Module.IsTorsion ℤ_[ℓ] (F.stalk x))

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
