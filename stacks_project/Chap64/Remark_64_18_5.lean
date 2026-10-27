/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Abelian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open scoped Pointwise

universe u

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/- Remark 64.18.5. Geometric component stalks form successive finite residue-ring
quotients; their inverse limit is a finite padic module with the decomposition
and canonical reductions checked below. -/
@[stacks 03UQ] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalk_finite :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    Module.Finite ℤ_[ℓ] (F.stalk x))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk_nsmul_eq_zero :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ)
    (y : F.componentStalk x n), (ℓ ^ (n + 1)) • y = 0)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk_finite :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ),
    Module.Finite (ZMod (ℓ ^ (n + 1))) (F.componentStalk x n))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk_step_surjective :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ+),
    Function.Surjective ((F.componentStalkSystem x).stepMap n.natPred).hom)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk_step_ker_nsmul :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ+),
    AddMonoidHom.ker ((F.componentStalkSystem x).stepMap n.natPred).hom =
      ((ℓ : ℤ) ^ (n : ℕ) • ⊤ :
        Submodule ℤ (F.componentStalk x (n.natPred + 1))).toAddSubgroup)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk_quot_nsmul_eq_zero :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ+)
    (y : (F.componentStalk x (n.natPred + 1)) ⧸
      ((ℓ : ℤ) ^ (n : ℕ) • ⊤ : Submodule ℤ (F.componentStalk x (n.natPred + 1)))),
    (ℓ ^ (n.natPred + 1)) • y = 0)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk_quot_succ_map :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ+),
    ((F.componentStalk x (n.natPred + 1)) ⧸
      ((ℓ : ℤ) ^ (n : ℕ) • ⊤ : Submodule ℤ (F.componentStalk x (n.natPred + 1))))
      →ₗ[ZMod (ℓ ^ (n.natPred + 1))] F.componentStalk x n.natPred)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk_quot_succ_map_bijective :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ+),
    Function.Bijective (F.componentStalk_quot_succ_map x n))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk_quot_succ_equiv :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ+),
    (F.componentStalk x n.natPred) ≃ₗ[ZMod (ℓ ^ (n.natPred + 1))]
      ((F.componentStalk x (n.natPred + 1)) ⧸
        ((ℓ : ℤ) ^ (n : ℕ) • ⊤ : Submodule ℤ (F.componentStalk x (n.natPred + 1)))))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.componentStalk_quot_succ_equiv_apply_mk :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X) (n : ℕ+)
    (y : F.componentStalk x (n.natPred + 1)),
    (F.componentStalk_quot_succ_equiv x n).symm (Submodule.Quotient.mk y) =
      ((F.componentStalkSystem x).stepMap n.natPred).hom y)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalkFirstProjection :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    F.stalk x →ₗ[ℤ_[ℓ]] F.componentStalk x 0)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalkFirstProjection_surjective :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    Function.Surjective (F.stalkFirstProjection x))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalkFirstProjection_ker :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    LinearMap.ker (F.stalkFirstProjection x) =
      (Ideal.span {(ℓ : ℤ_[ℓ])} • ⊤ : Submodule ℤ_[ℓ] (F.stalk x)))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalk_quot_ell_equiv_componentStalk :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    ((F.stalk x) ⧸
      (Ideal.span {(ℓ : ℤ_[ℓ])} • ⊤ : Submodule ℤ_[ℓ] (F.stalk x))) ≃ₗ[ℤ_[ℓ]]
      F.componentStalk x 0)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalk_quot_ell_equiv_componentStalk_apply_mk :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X)
    (m : F.stalk x),
    F.stalk_quot_ell_equiv_componentStalk x (Submodule.Quotient.mk m) =
      (F.stalk_π x 0).hom m)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.stalk_equiv_free_prod_ellPowerTorsion :
  ∀ (F : ZEllSheaf X ℓ) (x : GeometricPoint X),
    ∃ (r t : ℕ) (e : Fin t → ℕ),
      (∀ i, 0 < e i) ∧
        Nonempty
          ((F.stalk x) ≃ₗ[ℤ_[ℓ]]
            (Fin r → ℤ_[ℓ]) ×
              DirectSum (Fin t) fun i ↦ ℤ_[ℓ] ⧸ Ideal.span {(ℓ : ℤ_[ℓ]) ^ e i}))

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
