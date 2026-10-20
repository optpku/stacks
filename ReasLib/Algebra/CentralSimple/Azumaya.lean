/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.Basic
public import Mathlib.Algebra.Azumaya.Basic
public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.LinearAlgebra.Basis.MulOpposite
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Central Simple Algebras are Azumaya

Every finite-dimensional central simple k-algebra is Azumaya over k.

## Main declarations

- `CSA.instIsAzumaya` — the `IsAzumaya k A` instance for finite-dimensional central simple algebras

## References

- [Stacks Project, Tag 074I](https://stacks.math.columbia.edu/tag/074I)
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace CSA

variable {k : Type u} [Field k]
variable {A : Type v} [Ring A] [Algebra k A] [FiniteDimensional k A]
variable [Algebra.IsCentral k A] [IsSimpleRing A]

/-- The left-right multiplication map of a finite-dimensional central simple algebra is bijective. -/
private theorem mulLeftRight_bijective :
    Function.Bijective (AlgHom.mulLeftRight k A) := by
  let f : (A ⊗[k] Aᵐᵒᵖ) →ₗ[k] Module.End k A := (AlgHom.mulLeftRight k A).toLinearMap
  have h_inj : Function.Injective f := by
    exact @RingHom.injective (A ⊗[k] Aᵐᵒᵖ) (Module.End k A) _
      (isSimpleRing_tensorProduct_of_finite_central_left_factor (k := k) (A := A) (A' := Aᵐᵒᵖ))
      _ _ (AlgHom.mulLeftRight k A).toRingHom
  have h_op : Module.finrank k Aᵐᵒᵖ = Module.finrank k A := by
    simpa using
      (LinearEquiv.finrank_eq (MulOpposite.opLinearEquiv k : A ≃ₗ[k] Aᵐᵒᵖ)).symm
  have h_finrank :
      Module.finrank k (A ⊗[k] Aᵐᵒᵖ) = Module.finrank k (Module.End k A) := by
    calc
      Module.finrank k (A ⊗[k] Aᵐᵒᵖ)
          = Module.finrank k A * Module.finrank k A := by
              rw [Module.finrank_tensorProduct, h_op]
      _ = Module.finrank k (Module.End k A) := by
            symm
            simpa using (Module.finrank_linearMap k k A A)
  have h_surj : Function.Surjective (AlgHom.mulLeftRight k A) := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_finrank).mp h_inj
  exact ⟨h_inj, h_surj⟩

/-- Every finite-dimensional central simple algebra is Azumaya over its field. -/
instance instIsAzumaya : IsAzumaya k A where
  bij := mulLeftRight_bijective

/-- The left-right multiplication map identifies `A ⊗[k] Aᵐᵒᵖ` with `Module.End k A`
for a finite-dimensional central simple algebra `A`. -/
noncomputable def mulLeftRightAlgEquiv (A : CSA.{u, v} k) :
    A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Module.End k A :=
  AlgEquiv.ofBijective (AlgHom.mulLeftRight k A)
    (IsAzumaya.AlgHom.mulLeftRight_bij (R := k) (A := A))

end CSA

end
