/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra.Decomposition
public import ReasLib.LinearAlgebra.ExteriorAlgebra.Prod
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u v w

namespace ModuleCat.exteriorPower

variable {R : Type u} [CommRing R]

/-- Projection of an exterior algebra onto its homogeneous component of degree `n`. -/
noncomputable def homogeneousProjection (M : ModuleCat.{v} R) (n : ℕ) :
    ExteriorAlgebra R M →ₗ[R] M.exteriorPower n :=
  (DirectSum.component R ℕ (fun i : ℕ ↦ M.exteriorPower i) n).comp
    (DirectSum.decomposeLinearEquiv (fun i : ℕ ↦ ⋀[R]^i M)).toLinearMap

/-- Homogeneous projection is the identity on the corresponding exterior-power component. -/
@[simp]
theorem homogeneousProjection_coe (M : ModuleCat.{v} R) (n : ℕ)
    (x : M.exteriorPower n) :
    homogeneousProjection M n ((⋀[R]^n M).subtype x) = x := sorry

/-- Projection to bidegree `(p, q)` after identifying a module with a binary product. -/
noncomputable def bidegreeProjection {A B L : ModuleCat.{v} R}
    (e : ModuleCat.of R (A × B) ≅ L) (p q : ℕ) :
    L.exteriorPower (p + q) →ₗ[R] A.exteriorPower p ⊗[R] B.exteriorPower q :=
  (TensorProduct.map (homogeneousProjection A p) (homogeneousProjection B q)).comp
    ((ExteriorAlgebra.prodEquiv R A B).toLinearMap.comp
      ((ExteriorAlgebra.map e.inv.hom).toLinearMap.comp
        (ModuleCat.exteriorAlgebra.powerι L (p + q)).hom))

/-- The bidegree projection sends a concatenated left and right wedge to its pure tensor. -/
@[simp]
theorem bidegreeProjection_mk {A B L : ModuleCat.{v} R}
    (e : ModuleCat.of R (A × B) ≅ L) (p q : ℕ)
    (x : Fin p → A) (y : Fin q → B) :
    bidegreeProjection e p q
        (mk (Fin.append (fun i ↦ e.hom (x i, 0)) (fun j ↦ e.hom (0, y j)))) =
      mk x ⊗ₜ[R] mk y := sorry

/-- Descend a linear map through a surjective map on an exterior power. -/
noncomputable def descOfSurjective {M Q : ModuleCat.{v} R} {P : ModuleCat.{w} R}
    (q : M ⟶ Q) (n : ℕ)
    (hq : Function.Surjective (ModuleCat.exteriorPower.map q n))
    (f : M.exteriorPower n →ₗ[R] P)
    (hker : LinearMap.ker (ModuleCat.exteriorPower.map q n).hom ≤ LinearMap.ker f) :
    Q.exteriorPower n →ₗ[R] P :=
  (LinearMap.ker (ModuleCat.exteriorPower.map q n).hom).liftQ f hker |>.comp
    (((ModuleCat.exteriorPower.map q n).hom.quotKerEquivOfSurjective hq).symm.toLinearMap)

/-- The descended map recovers the original map after the given surjection. -/
theorem descOfSurjective_comp {M Q : ModuleCat.{v} R} {P : ModuleCat.{w} R}
    (q : M ⟶ Q) (n : ℕ)
    (hq : Function.Surjective (ModuleCat.exteriorPower.map q n))
    (f : M.exteriorPower n →ₗ[R] P)
    (hker : LinearMap.ker (ModuleCat.exteriorPower.map q n).hom ≤ LinearMap.ker f) :
    (descOfSurjective q n hq f hker).comp
        (ModuleCat.exteriorPower.map q n).hom = f := sorry

/-- A map out of the target of a surjection is determined by its composite with that
surjection. -/
theorem descOfSurjective_unique {M Q : ModuleCat.{v} R} {P : ModuleCat.{w} R}
    (q : M ⟶ Q) (n : ℕ)
    (hq : Function.Surjective (ModuleCat.exteriorPower.map q n))
    (f : M.exteriorPower n →ₗ[R] P)
    (hker : LinearMap.ker (ModuleCat.exteriorPower.map q n).hom ≤ LinearMap.ker f)
    (g : Q.exteriorPower n →ₗ[R] P)
    (hg : g.comp (ModuleCat.exteriorPower.map q n).hom = f) :
    g = descOfSurjective q n hq f hker := sorry

end ModuleCat.exteriorPower

end
