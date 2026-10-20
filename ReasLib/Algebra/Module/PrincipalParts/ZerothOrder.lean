/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.Functorial

/-!
# Zeroth principal parts

The zeroth principal-parts module is canonically the original module.  This file exposes the
comparison in both directions, its universal-class specification, and its naturality in the
module argument.

@stack 09CL
-/

@[expose] public section

universe u

noncomputable section

namespace PrincipalParts.ZerothOrder

variable {R S M N : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The identity of an `S`-module, restricted to `R`, is a differential operator of order zero. -/
theorem id_isDifferentialOperatorOfOrder :
    (LinearMap.restrictScalars R (LinearMap.id : M →ₗ[S] M)).IsDifferentialOperatorOfOrder S 0 :=
  sorry

/-- The canonical projection from zeroth principal parts to the original module. -/
noncomputable def projection : PrincipalParts.module R S M 0 →ₗ[S] M :=
  (representingEquiv R S M 0 M).symm
    ⟨LinearMap.restrictScalars R (LinearMap.id : M →ₗ[S] M),
      id_isDifferentialOperatorOfOrder (R := R) (S := S) (M := M)⟩

/-- The zeroth universal class is `S`-linear in its input. -/
theorem universalDifferential_smul (s : S) (m : M) :
    universalDifferential (R := R) (S := S) (M := M) 0 (s • m) =
      s • universalDifferential (R := R) (S := S) (M := M) 0 m := sorry

/-- The original module maps to zeroth principal parts by its universal class. -/
noncomputable def inclusion : M →ₗ[S] PrincipalParts.module R S M 0 where
  toFun := universalDifferential (R := R) (S := S) (M := M) 0
  map_add' := (universalDifferential (R := R) (S := S) (M := M) 0).map_add
  map_smul' := universalDifferential_smul (R := R) (S := S) (M := M)

/-- The zeroth projection sends a universal class back to its source element. -/
@[simp]
theorem projection_apply_universalDifferential (m : M) :
    projection (R := R) (S := S) (M := M)
        (universalDifferential (R := R) (S := S) (M := M) 0 m) = m := sorry

/-- Projection after inclusion is the identity of the original module. -/
@[simp]
theorem projection_comp_inclusion :
    (projection (R := R) (S := S) (M := M)).comp
        (inclusion (R := R) (S := S) (M := M)) = LinearMap.id := sorry

/-- Inclusion after projection is the identity of zeroth principal parts. -/
@[simp]
theorem inclusion_comp_projection :
    (inclusion (R := R) (S := S) (M := M)).comp
        (projection (R := R) (S := S) (M := M)) = LinearMap.id := sorry

/-- Tag 09CL: zeroth principal parts are canonically linearly equivalent to the original
module. -/
@[stacks 09CL "zeroth principal parts"]
noncomputable def equiv : PrincipalParts.module R S M 0 ≃ₗ[S] M :=
  LinearEquiv.ofLinear
    (projection (R := R) (S := S) (M := M))
    (inclusion (R := R) (S := S) (M := M))
    (projection_comp_inclusion (R := R) (S := S) (M := M))
    (inclusion_comp_projection (R := R) (S := S) (M := M))

variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The zeroth principal-parts projection is natural in the module argument. -/
theorem projection_naturality (f : M →ₗ[S] N) :
    (projection (R := R) (S := S) (M := N)).comp
        (PrincipalParts.map (R := R) (S := S) 0 f) =
      f.comp (projection (R := R) (S := S) (M := M)) := sorry

/-- The inverse zeroth-principal-parts map is natural in the module argument. -/
theorem inclusion_naturality (f : M →ₗ[S] N) :
    (PrincipalParts.map (R := R) (S := S) 0 f).comp
        (inclusion (R := R) (S := S) (M := M)) =
      (inclusion (R := R) (S := S) (M := N)).comp f := sorry

end PrincipalParts.ZerothOrder
