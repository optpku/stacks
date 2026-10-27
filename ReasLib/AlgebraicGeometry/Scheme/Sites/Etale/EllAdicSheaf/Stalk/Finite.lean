/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Finiteness.Defs

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open scoped Pointwise

universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (F : ZEllSheaf X ℓ)

noncomputable section

/-- Component stalks of an integral ℓ-adic sheaf are annihilated by `ℓ^(n+1)`.
Stage `n` corresponds to the component indexed by `n+1`. -/
theorem componentStalk_nsmul_eq_zero (x : GeometricPoint X) (n : ℕ)
    (y : F.componentStalk x n) : (ℓ ^ (n + 1)) • y = 0 := sorry

/-- The residue-ring module structure on a component stalk. -/
instance instModuleComponentStalk (x : GeometricPoint X) (n : ℕ) :
    Module (ZMod (ℓ ^ (n + 1))) (F.componentStalk x n) :=
  AddCommGroup.zmodModule (componentStalk_nsmul_eq_zero F x n)

/-- Restriction of scalars along `ℤ_[ℓ] → ZMod (ℓ^(n+1))` on a component stalk. -/
instance instModuleComponentStalkPadic (x : GeometricPoint X) (n : ℕ) :
    Module ℤ_[ℓ] (F.componentStalk x n) :=
  Module.compHom (F.componentStalk x n) (PadicInt.toZModPow (n + 1))

/-- Each geometric component stalk is finite over its residue ring. -/
instance componentStalk_finite (x : GeometricPoint X) (n : ℕ) :
    Module.Finite (ZMod (ℓ ^ (n + 1))) (F.componentStalk x n) := sorry

/-- The successor transition on geometric component stalks is surjective. -/
theorem componentStalk_step_surjective (x : GeometricPoint X) (n : ℕ+) :
    Function.Surjective ((F.componentStalkSystem x).stepMap n.natPred).hom := sorry

/-- The successor transition has kernel `ℓ^n` times the next component stalk. -/
theorem componentStalk_step_ker_nsmul (x : GeometricPoint X) (n : ℕ+) :
    AddMonoidHom.ker ((F.componentStalkSystem x).stepMap n.natPred).hom =
      ((ℓ : ℤ) ^ (n : ℕ) • ⊤ :
        Submodule ℤ (F.componentStalk x (n.natPred + 1))).toAddSubgroup := sorry

/-- The quotient of the next component by `ℓ^n` is annihilated by that power. -/
theorem componentStalk_quot_nsmul_eq_zero (x : GeometricPoint X) (n : ℕ+)
    (y : (F.componentStalk x (n.natPred + 1)) ⧸
      ((ℓ : ℤ) ^ (n : ℕ) • ⊤ : Submodule ℤ (F.componentStalk x (n.natPred + 1)))) :
    (ℓ ^ (n.natPred + 1)) • y = 0 := sorry

/-- The residue-ring module structure on a successive quotient of component stalks. -/
instance instModuleComponentStalkQuot (x : GeometricPoint X) (n : ℕ+) :
    Module (ZMod (ℓ ^ (n.natPred + 1)))
      ((F.componentStalk x (n.natPred + 1)) ⧸
        ((ℓ : ℤ) ^ (n : ℕ) • ⊤ : Submodule ℤ (F.componentStalk x (n.natPred + 1)))) :=
  AddCommGroup.zmodModule (componentStalk_quot_nsmul_eq_zero F x n)

/-- The linear map induced by the successor transition on its successive quotient. -/
def componentStalk_quot_succ_map (x : GeometricPoint X) (n : ℕ+) :
    ((F.componentStalk x (n.natPred + 1)) ⧸
      ((ℓ : ℤ) ^ (n : ℕ) • ⊤ : Submodule ℤ (F.componentStalk x (n.natPred + 1))))
      →ₗ[ZMod (ℓ ^ (n.natPred + 1))] F.componentStalk x n.natPred :=
  AddMonoidHom.toZModLinearMap (ℓ ^ (n.natPred + 1))
    (M₁ := F.componentStalk x n.natPred)
    (((ℓ : ℤ) ^ (n : ℕ) • ⊤ : Submodule ℤ (F.componentStalk x (n.natPred + 1))).liftQ
    (((F.componentStalkSystem x).stepMap n.natPred).hom :
      F.componentStalk x (n.natPred + 1) →+ F.componentStalk x n.natPred).toIntLinearMap (by
      intro y hy
      change ((F.componentStalkSystem x).stepMap n.natPred).hom y = 0
      change y ∈ ((ℓ : ℤ) ^ (n : ℕ) • ⊤ :
        Submodule ℤ (F.componentStalk x (n.natPred + 1))).toAddSubgroup at hy
      rwa [← F.componentStalk_step_ker_nsmul x n] at hy)).toAddMonoidHom

/-- The map induced by the successor transition on its quotient is bijective. -/
theorem componentStalk_quot_succ_map_bijective (x : GeometricPoint X) (n : ℕ+) :
    Function.Bijective (F.componentStalk_quot_succ_map x n) := sorry

/-- A component stalk is canonically the quotient of the next stalk by `ℓ^n`. -/
def componentStalk_quot_succ_equiv (x : GeometricPoint X) (n : ℕ+) :
    (F.componentStalk x n.natPred) ≃ₗ[ZMod (ℓ ^ (n.natPred + 1))]
      ((F.componentStalk x (n.natPred + 1)) ⧸
        ((ℓ : ℤ) ^ (n : ℕ) • ⊤ : Submodule ℤ (F.componentStalk x (n.natPred + 1)))) :=
  (LinearEquiv.ofBijective (F.componentStalk_quot_succ_map x n)
    (F.componentStalk_quot_succ_map_bijective x n)).symm

/-- The inverse quotient comparison sends a representative to its successor-transition image. -/
theorem componentStalk_quot_succ_equiv_apply_mk (x : GeometricPoint X) (n : ℕ+)
    (y : F.componentStalk x (n.natPred + 1)) :
    (F.componentStalk_quot_succ_equiv x n).symm (Submodule.Quotient.mk y) =
      ((F.componentStalkSystem x).stepMap n.natPred).hom y := sorry

/-- The first inverse-limit projection as a padic-linear map. -/
def stalkFirstProjection (x : GeometricPoint X) :
    F.stalk x →ₗ[ℤ_[ℓ]] F.componentStalk x 0 where
  toFun := (F.stalk_π x 0).hom
  map_add' := (F.stalk_π x 0).hom.map_add
  map_smul' := sorry

/-- The first inverse-limit projection is surjective. -/
theorem stalkFirstProjection_surjective (x : GeometricPoint X) :
    Function.Surjective (F.stalkFirstProjection x) := sorry

/-- The kernel of the first inverse-limit projection is `ℓ` times the stalk. -/
theorem stalkFirstProjection_ker (x : GeometricPoint X) :
    LinearMap.ker (F.stalkFirstProjection x) =
      (Ideal.span {(ℓ : ℤ_[ℓ])} • ⊤ : Submodule ℤ_[ℓ] (F.stalk x)) := sorry

/-- Reduction of a geometric stalk modulo `ℓ` is canonically its first component stalk. -/
def stalk_quot_ell_equiv_componentStalk (x : GeometricPoint X) :
    ((F.stalk x) ⧸
      (Ideal.span {(ℓ : ℤ_[ℓ])} • ⊤ : Submodule ℤ_[ℓ] (F.stalk x))) ≃ₗ[ℤ_[ℓ]]
      F.componentStalk x 0 :=
  (Submodule.quotEquivOfEq _ _ (F.stalkFirstProjection_ker x).symm).trans
    ((F.stalkFirstProjection x).quotKerEquivOfSurjective
      (F.stalkFirstProjection_surjective x))

/-- The reduction comparison sends a stalk representative to its first component. -/
theorem stalk_quot_ell_equiv_componentStalk_apply_mk (x : GeometricPoint X)
    (m : F.stalk x) :
    F.stalk_quot_ell_equiv_componentStalk x (Submodule.Quotient.mk m) =
      (F.stalk_π x 0).hom m := sorry

/-- The geometric inverse-limit stalk of an integral ℓ-adic sheaf is a finite padic module. -/
instance stalk_finite (x : GeometricPoint X) :
    Module.Finite ℤ_[ℓ] (F.stalk x) := sorry

/-- A geometric stalk is a finite free padic module times finitely many cyclic quotients
by strictly positive powers of `ℓ`. -/
theorem stalk_equiv_free_prod_ellPowerTorsion (x : GeometricPoint X) :
    ∃ (r t : ℕ) (e : Fin t → ℕ),
      (∀ i, 0 < e i) ∧
        Nonempty
          ((F.stalk x) ≃ₗ[ℤ_[ℓ]]
            (Fin r → ℤ_[ℓ]) ×
              DirectSum (Fin t) fun i ↦ ℤ_[ℓ] ⧸ Ideal.span {(ℓ : ℤ_[ℓ]) ^ e i}) := sorry

end

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
