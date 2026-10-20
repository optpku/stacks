/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap64.Remark_64_18_7_ZEllSheaf
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory
open scoped Pointwise

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (F : ZEllSheaf X ℓ)

noncomputable section

/-- Component stalks of a `ℤ_[ℓ]`-sheaf are annihilated by `ℓ^{n+1}`. -/
theorem componentStalk_nsmul_eq_zero (x : GeometricPoint X) (n : ℕ)
    (y : F.componentStalk x n) : (ℓ ^ (n + 1)) • y = 0 := sorry

/-- Canonical `ZMod (ℓ^{n+1})`-module structure on a component stalk. -/
instance instModuleComponentStalk (x : GeometricPoint X) (n : ℕ) :
    Module (ZMod (ℓ ^ (n + 1))) (F.componentStalk x n) :=
  AddCommGroup.zmodModule (componentStalk_nsmul_eq_zero F x n)

/-- Source-indexed component stalks `M_n` are annihilated by `ℓ^n`. -/
theorem componentStalk_nsmul_eq_zero_pnat (x : GeometricPoint X) (n : ℕ+)
    (y : F.componentStalk x n.natPred) : (ℓ ^ (n : ℕ)) • y = 0 := sorry

/-- Restriction of scalars along `ℤ_[ℓ] → ZMod (ℓ^{n+1})` on a component stalk. -/
instance instModuleComponentStalkPadic (x : GeometricPoint X) (n : ℕ) :
    Module ℤ_[ℓ] (F.componentStalk x n) :=
  Module.compHom (F.componentStalk x n) (PadicInt.toZModPow (n + 1))

/-- Remark 64.18.5 (1): for a constructible `ℤ_[ℓ]`-sheaf, each geometric component
stalk `M_n = F_{n, x̄}` is a finite `ZMod (ℓ^n)`-module. The coefficient ring is
written `ZMod (ℓ ^ (n.natPred + 1))`; `PNat.natPred_add_one` identifies the exponent
with `(n : ℕ)`. -/
@[stacks 03UQ]
theorem componentStalk_finite
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (x : GeometricPoint X) (n : ℕ+) :
    Module.Finite (ZMod (ℓ ^ (n.natPred + 1))) (F.componentStalk x n.natPred) := sorry

/-- The successor map on component stalks is surjective. -/
theorem componentStalk_step_surjective (x : GeometricPoint X) (n : ℕ+) :
    Function.Surjective ((F.componentStalkSystem x).stepMap n.natPred).hom := sorry

/-- The kernel of the successor map on component stalks is `ℓ^n` times the next stalk. -/
theorem componentStalk_step_ker_nsmul (x : GeometricPoint X) (n : ℕ+) :
    AddMonoidHom.ker ((F.componentStalkSystem x).stepMap n.natPred).hom =
      ((ℓ : ℤ) ^ (n : ℕ) • ⊤ :
        Submodule ℤ (F.componentStalk x (n.natPred + 1))).toAddSubgroup :=
  sorry

/-- Successive quotients of component stalks are annihilated by `ℓ^n`. -/
theorem componentStalk_quot_nsmul_eq_zero (x : GeometricPoint X) (n : ℕ+)
    (y : (F.componentStalk x (n.natPred + 1)) ⧸
      ((ℓ : ℤ) ^ (n : ℕ) • ⊤ : Submodule ℤ (F.componentStalk x (n.natPred + 1)))) :
    (ℓ ^ (n.natPred + 1)) • y = 0 := sorry

/-- Canonical `ZMod (ℓ ^ (n.natPred + 1))`-module structure on the successive quotient
of component stalks. -/
instance instModuleComponentStalkQuot (x : GeometricPoint X) (n : ℕ+) :
    Module (ZMod (ℓ ^ (n.natPred + 1)))
      ((F.componentStalk x (n.natPred + 1)) ⧸
        ((ℓ : ℤ) ^ (n : ℕ) • ⊤ : Submodule ℤ (F.componentStalk x (n.natPred + 1)))) :=
  AddCommGroup.zmodModule (componentStalk_quot_nsmul_eq_zero F x n)

/-- Remark 64.18.5 (2): successor maps on geometric component stalks are successive
quotients, identifying `M_n` with `M_{n+1} / ℓ^n M_{n+1}`. The linear equivalence is
over `ZMod (ℓ ^ (n.natPred + 1))`; `PNat.natPred_add_one` identifies the exponent with
`(n : ℕ)`. -/
@[stacks 03UQ]
theorem componentStalk_quot_succ_equiv (x : GeometricPoint X) (n : ℕ+) :
    Nonempty
      ((F.componentStalk x n.natPred) ≃ₗ[ZMod (ℓ ^ (n.natPred + 1))]
        ((F.componentStalk x (n.natPred + 1)) ⧸
          ((ℓ : ℤ) ^ (n : ℕ) • ⊤ :
            Submodule ℤ (F.componentStalk x (n.natPred + 1))))) := sorry

/-- Remark 64.18.5 (3): the geometric stalk `F.stalk x = lim F_{n, x̄}` of a constructible
`ℤ_[ℓ]`-sheaf is a finite `ℤ_[ℓ]`-module. This follows from Algebra, Lemmas 10.98.2 and
10.96.12, together with `M / ℓ M = M_1` being finite over `ZMod ℓ`. -/
@[stacks 03UQ]
theorem stalk_finite
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (x : GeometricPoint X) :
    Module.Finite ℤ_[ℓ] (F.stalk x) := sorry

/-- The reduction of a geometric stalk modulo `ℓ` recovers the first component stalk. -/
theorem stalk_quot_ell_equiv_componentStalk (x : GeometricPoint X) :
    Nonempty
      (((F.stalk x) ⧸
          (Ideal.span {(ℓ : ℤ_[ℓ])} • ⊤ : Submodule ℤ_[ℓ] (F.stalk x))) ≃ₗ[ℤ_[ℓ]]
        F.componentStalk x 0) := sorry

/-- Remark 64.18.5 (4): a constructible geometric stalk decomposes as a finite free
`ℤ_[ℓ]`-module times a direct sum of cyclic `ℓ`-power torsion modules. -/
@[stacks 03UQ]
theorem stalk_equiv_free_prod_ellPowerTorsion
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (x : GeometricPoint X) :
    ∃ (r t : ℕ) (e : Fin t → ℕ),
      (∀ i, 0 < e i) ∧
        Nonempty
          ((F.stalk x) ≃ₗ[ℤ_[ℓ]]
            (Fin r → ℤ_[ℓ]) ×
              DirectSum (Fin t) fun i ↦ ℤ_[ℓ] ⧸ Ideal.span {(ℓ : ℤ_[ℓ]) ^ e i}) :=
  sorry

end

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
