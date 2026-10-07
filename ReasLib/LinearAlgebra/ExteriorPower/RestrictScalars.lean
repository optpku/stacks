module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import ReasLib.LinearAlgebra.PiTensorProduct.RestrictScalars

@[expose] public section

open scoped TensorProduct

/-!
# Restriction of scalars for exterior powers

This file provides the exterior-power map induced by an `R`-linear map into an `S`-module,
viewed over `R` through an algebra `R →ₐ S`.  Its codomain uses mathlib's `RestrictScalars` type
alias, so the canonical restricted module structure does not compete with other scalar actions on
the underlying exterior power.

@stack 0H1C
-/

namespace exteriorPower

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The map on degree-`n` exterior powers induced by an `R`-linear map to an `S`-module.

The target is the canonical `RestrictScalars` alias. The required scalar tower on `N` ensures
that the restricted `S`-multilinear generator is `R`-multilinear. -/
@[stacks 0H1C "exterior-power scalar restriction"]
noncomputable def restrictScalarsMap (n : ℕ) (f : M →ₗ[R] N) :
    ⋀[R]^n M →ₗ[R] RestrictScalars R S (⋀[S]^n N) := by
  let iotaN' : N [⋀^Fin n]→ₗ[R] RestrictScalars R S (⋀[S]^n N) := by
    exact
      { toMultilinearMap :=
          { toFun := ιMulti S n
            map_update_add' := by
              intro _ m i x y
              exact (ιMulti S n).toMultilinearMap.map_update_add m i x y
            map_update_smul' := by
              intro _ m i r x
              change ιMulti S n (Function.update m i (r • x)) =
                algebraMap R S r • ιMulti S n (Function.update m i x)
              rw [← IsScalarTower.algebraMap_smul S r x]
              exact (ιMulti S n).toMultilinearMap.map_update_smul
                m i (algebraMap R S r) x }
        map_eq_zero_of_eq' := by
          intro m i j hij hne
          exact (ιMulti S n).map_eq_zero_of_eq m hij hne }
  exact @alternatingMapLinearEquiv R _ n M (RestrictScalars R S (⋀[S]^n N)) _ _ _
    (RestrictScalars.module R S (⋀[S]^n N)) (iotaN'.compLinearMap f)

/-- `restrictScalarsMap` sends an alternating generator to the alternating product of its
entrywise image. -/
@[simp, stacks 0H1C "exterior-power scalar restriction on generators"]
theorem restrictScalarsMap_apply_ιMulti (n : ℕ) (f : M →ₗ[R] N) (m : Fin n → M) :
    restrictScalarsMap (R := R) (S := S) n f (ιMulti R n m) =
      (ιMulti S n (f ∘ m) : RestrictScalars R S (⋀[S]^n N)) := sorry

/-- The canonical map from the tensor power over `R` to the exterior power over
`S`, induced entrywise by `f`. -/
@[stacks 0H1C "tensor-to-exterior scalar restriction"]
noncomputable def restrictScalarsQuotient (n : ℕ) (f : M →ₗ[R] N) :
    (⨂[R]^n M) →ₗ[R] RestrictScalars R S (⋀[S]^n N) :=
  (RestrictScalars.map (R := R) (S := S)
    (PiTensorProduct.lift (ιMulti S n).toMultilinearMap)).comp
      (PiTensorProduct.restrictScalarsMap (R := R) (S := S) (fun _ ↦ f))

/-- `restrictScalarsQuotient` sends a pure tensor to the exterior product of
the entrywise images. -/
@[simp, stacks 0H1C "tensor-to-exterior scalar restriction on pure tensors"]
theorem restrictScalarsQuotient_tprod (n : ℕ) (f : M →ₗ[R] N) (m : Fin n → M) :
    restrictScalarsQuotient (R := R) (S := S) n f (PiTensorProduct.tprod R m) =
      (ιMulti S n (f ∘ m) : RestrictScalars R S (⋀[S]^n N)) := by
  simp [restrictScalarsQuotient, Function.comp_def]

/-- The tensor-to-exterior comparison factors through the tensor power after
changing the coefficient ring. -/
@[stacks 0H1C "tensor-to-exterior scalar restriction through target tensors"]
theorem restrictScalarsQuotient_factor (n : ℕ) (f : M →ₗ[R] N) :
    restrictScalarsQuotient (R := R) (S := S) n f =
      (RestrictScalars.map (R := R) (S := S)
        (PiTensorProduct.lift (ιMulti S n).toMultilinearMap)).comp
        (PiTensorProduct.restrictScalarsMap (R := R) (S := S) (fun _ ↦ f)) :=
  rfl

/-- The tensor-to-exterior comparison also factors through the exterior power over the source
ring, followed by the map on exterior powers after restricting scalars. -/
@[stacks 0H1C "tensor-to-exterior scalar restriction through the source exterior power"]
theorem restrictScalarsQuotient_factor_exteriorPower (n : ℕ) (f : M →ₗ[R] N) :
    restrictScalarsQuotient (R := R) (S := S) n f =
      (restrictScalarsMap (R := R) (S := S) n f).comp
        (PiTensorProduct.lift (ιMulti R n).toMultilinearMap) := by
  apply PiTensorProduct.ext
  ext m
  simp [restrictScalarsQuotient, Function.comp_def]

end

namespace RestrictScalars

section Bundled

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module S N]

/-- The exterior-power map induced by a map into the canonical restriction of
an `S`-module.  This is the structure-minimal entry point: the raw target
carrier needs no additional `R`-module or scalar-tower instances. -/
@[stacks 0H1C "bundled exterior-power scalar restriction"]
noncomputable def map (n : ℕ)
    (f : M →ₗ[R] _root_.RestrictScalars R S N) :
    ⋀[R]^n M →ₗ[R] _root_.RestrictScalars R S (⋀[S]^n N) := by
  -- Local instance justification (defeq pin): the raw target action must coincide definitionally with the bundled restriction of scalars.
  letI : Module R N := Module.restrictScalars R S N
  -- Local instance justification (defeq pin): the scalar tower must use the pinned restriction action for the exterior-power adapter.
  letI : IsScalarTower R S N := IsScalarTower.restrictScalars R S N
  exact exteriorPower.restrictScalarsMap (R := R) (S := S) (N := N) n
    (show M →ₗ[R] N from f)

/-- `map` sends an exterior generator to the exterior product of its
entrywise image. -/
@[simp, stacks 0H1C "bundled exterior restriction on generators"]
theorem map_ιMulti (n : ℕ)
    (f : M →ₗ[R] _root_.RestrictScalars R S N) (m : Fin n → M) :
    map (R := R) (S := S) n f (ιMulti R n m) =
      (ιMulti S n (fun i ↦ _root_.RestrictScalars.addEquiv R S N (f (m i))) :
        _root_.RestrictScalars R S (⋀[S]^n N)) := by
  -- Local instance justification (defeq pin): the generator formula uses the raw target with the same restriction action as map.
  letI : Module R N := Module.restrictScalars R S N
  -- Local instance justification (defeq pin): the generator adapter requires the tower for that pinned restriction action.
  letI : IsScalarTower R S N := IsScalarTower.restrictScalars R S N
  exact exteriorPower.restrictScalarsMap_apply_ιMulti
    (R := R) (S := S) (N := N) n (show M →ₗ[R] N from f) m

/-- The tensor-to-exterior map induced by a map into a canonical restriction
of scalars. -/
@[stacks 0H1C "bundled tensor-to-exterior scalar restriction"]
noncomputable def quotient (n : ℕ)
    (f : M →ₗ[R] _root_.RestrictScalars R S N) :
    (⨂[R]^n M) →ₗ[R] _root_.RestrictScalars R S (⋀[S]^n N) :=
  (_root_.RestrictScalars.map (R := R) (S := S)
    (PiTensorProduct.lift (ιMulti S n).toMultilinearMap)).comp
      (PiTensorProduct.RestrictScalars.map (R := R) (S := S) (fun _ ↦ f))

/-- `quotient` sends a pure tensor to the exterior product of its entrywise
image. -/
@[simp, stacks 0H1C "bundled tensor-to-exterior map on pure tensors"]
theorem quotient_tprod (n : ℕ)
    (f : M →ₗ[R] _root_.RestrictScalars R S N) (m : Fin n → M) :
    quotient (R := R) (S := S) n f (PiTensorProduct.tprod R m) =
      (ιMulti S n (fun i ↦ _root_.RestrictScalars.addEquiv R S N (f (m i))) :
        _root_.RestrictScalars R S (⋀[S]^n N)) := by
  simp [quotient]
  rfl

/-- The bundled tensor-to-exterior map factors through the tensor power over
the target ring. -/
@[stacks 0H1C "factorization of bundled tensor-to-exterior restriction"]
theorem quotient_factor (n : ℕ)
    (f : M →ₗ[R] _root_.RestrictScalars R S N) :
    quotient (R := R) (S := S) n f =
      (_root_.RestrictScalars.map (R := R) (S := S)
        (PiTensorProduct.lift (ιMulti S n).toMultilinearMap)).comp
        (PiTensorProduct.RestrictScalars.map (R := R) (S := S) (fun _ ↦ f)) :=
  rfl

/-- The bundled tensor-to-exterior map also factors through the source
exterior power. -/
@[stacks 0H1C "bundled tensor-to-exterior restriction through exterior power"]
theorem quotient_factor_exteriorPower (n : ℕ)
    (f : M →ₗ[R] _root_.RestrictScalars R S N) :
    quotient (R := R) (S := S) n f =
      (map (R := R) (S := S) n f).comp
        (PiTensorProduct.lift (ιMulti R n).toMultilinearMap) := by
  apply PiTensorProduct.ext
  ext m
  simp [quotient]
  rfl

end Bundled

end RestrictScalars

end exteriorPower
