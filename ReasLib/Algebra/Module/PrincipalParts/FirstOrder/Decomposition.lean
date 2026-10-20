/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.FirstOrder
public import ReasLib.Algebra.Module.PrincipalParts.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# First Principal Parts and Kähler Differentials

This leaf derives the first-principal-parts decomposition from the generic
first-order differential-operator splitting and the representing equivalence.
It deliberately keeps the decomposition separate from the first-principal-parts
short-exact-sequence API.

@stack 09CM
-/

@[expose] public section

universe u

noncomputable section

open KaehlerDifferential
namespace PrincipalParts.FirstOrder

section Representation

variable {R S M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M]
variable [IsScalarTower R S M]

/-- The maps out of first principal parts are equivalently a cotangent component and a value
component. -/
noncomputable def representingEquivCotangentProd :
    (PrincipalParts.module R S S 1 →ₗ[S] M) ≃ₗ[S] (Ω[S⁄R] →ₗ[S] M) × M :=
  (PrincipalParts.representingEquiv R S S 1 M).trans
    (DifferentialOperator.FirstOrder.equivCotangentProd (R := R) (S := S) (N := M))

end Representation

section Decomposition

variable {R S : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- The canonical map from first principal parts of `S` to the cotangent-and-value product. -/
noncomputable def toCotangentProd :
    PrincipalParts.module R S S 1 →ₗ[S] Ω[S⁄R] × S :=
  (representingEquivCotangentProd (R := R) (S := S) (M := Ω[S⁄R] × S)).symm
    (LinearMap.inl S Ω[S⁄R] S, ((0 : Ω[S⁄R]), (1 : S)))

/-- The cotangent and value components of the identity on first principal parts. -/
noncomputable def identityDecomposition :
    (Ω[S⁄R] →ₗ[S] PrincipalParts.module R S S 1) × PrincipalParts.module R S S 1 :=
  representingEquivCotangentProd (R := R) (S := S)
    (M := PrincipalParts.module R S S 1)
    (LinearMap.id : PrincipalParts.module R S S 1 →ₗ[S] PrincipalParts.module R S S 1)

/-- The map from the cotangent-and-value product back to first principal parts. -/
noncomputable def fromCotangentProd :
    Ω[S⁄R] × S →ₗ[S] PrincipalParts.module R S S 1 :=
  (identityDecomposition (R := R) (S := S)).1.coprod
    (LinearMap.smulRight (LinearMap.id : S →ₗ[S] S)
      (identityDecomposition (R := R) (S := S)).2)

/-- The cotangent-and-value map followed by its recombination map is the identity. -/
theorem toCotangentProd_comp_from :
    (toCotangentProd (R := R) (S := S)).comp
        (fromCotangentProd (R := R) (S := S)) =
      (LinearMap.id : Ω[S⁄R] × S →ₗ[S] Ω[S⁄R] × S) := sorry

/-- The recombination map followed by the cotangent-and-value map is the identity. -/
theorem fromCotangentProd_comp_to :
    (fromCotangentProd (R := R) (S := S)).comp
        (toCotangentProd (R := R) (S := S)) =
      (LinearMap.id : PrincipalParts.module R S S 1 →ₗ[S]
        PrincipalParts.module R S S 1) := sorry

/-- Example 10.133.5 (3), tag 09CM: first principal parts of an `R`-algebra `S` split
canonically as `Ω[S⁄R] × S`. -/
@[stacks 09CM]
noncomputable def equivCotangentProd :
    PrincipalParts.module R S S 1 ≃ₗ[S] Ω[S⁄R] × S :=
  LinearEquiv.ofLinear
    (toCotangentProd (R := R) (S := S))
    (fromCotangentProd (R := R) (S := S))
    (toCotangentProd_comp_from (R := R) (S := S))
    (fromCotangentProd_comp_to (R := R) (S := S))

/-- The forward map of the first-principal-parts decomposition is the canonical
cotangent-and-value map. -/
@[simp, stacks 09CM "first principal parts decomposition forward map"]
theorem equivCotangentProd_apply (x : PrincipalParts.module R S S 1) :
    equivCotangentProd (R := R) (S := S) x =
      toCotangentProd (R := R) (S := S) x := sorry

/-- The inverse map of the first-principal-parts decomposition is the canonical
recombination map. -/
@[simp, stacks 09CM "first principal parts decomposition inverse map"]
theorem equivCotangentProd_symm_apply (x : Ω[S⁄R] × S) :
    (equivCotangentProd (R := R) (S := S)).symm x =
      fromCotangentProd (R := R) (S := S) x := sorry

end Decomposition

section Naturality

variable {R S M M' : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M]
variable [IsScalarTower R S M]
variable [AddCommGroup M'] [Module S M'] [Module R M']
variable [IsScalarTower R S M']

/-- The cotangent-and-value representation of maps out of first principal parts is natural under
postcomposition in the target module. -/
theorem representingEquivCotangentProd_natural (f : M →ₗ[S] M')
    (L : PrincipalParts.module R S S 1 →ₗ[S] M) :
    representingEquivCotangentProd (R := R) (S := S) (M := M') (f.comp L) =
      ((LinearMap.compRight S f)
          (representingEquivCotangentProd (R := R) (S := S) (M := M) L).1,
        f (representingEquivCotangentProd (R := R) (S := S) (M := M) L).2) := sorry

end Naturality

end PrincipalParts.FirstOrder
