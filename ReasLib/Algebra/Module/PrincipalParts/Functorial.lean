/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.Basic
public import Mathlib.Algebra.Algebra.RestrictScalars

/-!
# Functoriality of Principal Parts

This leaf owns the covariant module functoriality of principal parts for a
fixed commutative algebra `R → S`.  Base change of the rings belongs in the
separate `PrincipalParts.BaseChange` namespace.

@stack 09CN
-/

@[expose] public section

universe u

noncomputable section

namespace PrincipalParts

variable {R S M N P : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The composite of an `S`-linear map with the universal differential on its target has
differential-operator order at most `k`. -/
theorem map_mem (k : ℕ) (f : M →ₗ[S] N) :
    ((universalDifferential (R := R) (S := S) (M := N) k).comp
      (f.restrictScalars R)) ∈
      differentialOperatorsOrderLESubmodule R S M k (PrincipalParts.module R S N k) :=
  sorry

/-- The map on `k`-th principal parts induced by an `S`-linear map of modules over the
fixed commutative algebra `R → S`. -/
@[stacks 09CN]
noncomputable def map (k : ℕ) (f : M →ₗ[S] N) :
    PrincipalParts.module R S M k →ₗ[S] PrincipalParts.module R S N k :=
  (representingEquiv R S M k (PrincipalParts.module R S N k)).symm
    ⟨(universalDifferential (R := R) (S := S) (M := N) k).comp
        (f.restrictScalars R),
      map_mem k f⟩

/-- The principal-parts map induced by `f` sends a universal class to the universal class of
its image. -/
@[simp]
theorem map_apply_universalDifferential (k : ℕ) (f : M →ₗ[S] N) (m : M) :
    map (R := R) (S := S) k f
        (universalDifferential (R := R) (S := S) (M := M) k m) =
      universalDifferential (R := R) (S := S) (M := N) k (f m) :=
  sorry

section Identity

/-- Principal-parts functoriality sends the identity map of a module to the identity map. -/
@[simp]
theorem map_id (k : ℕ) :
    map (R := R) (S := S) k (LinearMap.id : M →ₗ[S] M) = LinearMap.id :=
  sorry

end Identity

section Composition

variable [AddCommGroup P] [Module S P] [Module R P] [IsScalarTower R S P]

/-- Principal-parts functoriality preserves composition of module maps. -/
@[simp]
theorem map_comp (k : ℕ) (f : M →ₗ[S] N) (g : N →ₗ[S] P) :
    map (R := R) (S := S) k (g.comp f) =
      (map (R := R) (S := S) k g).comp (map (R := R) (S := S) k f) :=
  sorry

end Composition

end PrincipalParts

end
