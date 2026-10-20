module

public import ReasLib.LinearAlgebra.ExteriorPower.RestrictScalars
public import ReasLib.LinearAlgebra.TensorPower.Insertion.Exterior

/-!
# Exterior-power presentations under restriction of scalars

The kernel is expressed as the inverse image of the intrinsic repeated-entry
relations in the target tensor power.  The input map is arbitrary; the
scalar-tower comparison is the identity-map specialization.

@stack 0H1C
-/

@[expose] public section

open scoped TensorProduct

namespace exteriorPower

universe uR uS uM uN

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- The tensor-to-exterior kernel after changing scalars is the inverse image
of the target's intrinsic repeated-entry relation submodule. -/
@[stacks 0H1C "exterior presentation under restriction of scalars"]
theorem ker_restrictScalarsQuotient (n : ℕ) (f : M →ₗ[R] N) :
    (restrictScalarsQuotient (R := R) (S := S) n f).ker =
      Submodule.comap
        (PiTensorProduct.restrictScalarsMap (R := R) (S := S)
          (fun _ : Fin n ↦ f))
        (RestrictScalars.span (R := R) (S := S)
          (TensorPower.Insertion.Exterior.repeatSet (R := S) (M := N) n)) := by
  rw [restrictScalarsQuotient_factor, LinearMap.ker_comp,
    RestrictScalars.ker_map,
    TensorPower.Insertion.Exterior.ker_eq_span_repeatSet]
  rfl

namespace RestrictScalars

section Bundled

variable {M : Type uM} [AddCommGroup M] [Module R M]
variable {N : Type uN} [AddCommGroup N] [Module S N]

/-- The kernel of the structure-minimal tensor-to-exterior map is the
preimage of the intrinsic repeated-entry relations in the target tensor
power. -/
@[stacks 0H1C "bundled exterior presentation under scalar restriction"]
theorem ker_quotient (n : ℕ)
    (f : M →ₗ[R] _root_.RestrictScalars R S N) :
    (quotient (R := R) (S := S) n f).ker =
      Submodule.comap
        (PiTensorProduct.RestrictScalars.map (R := R) (S := S)
          (fun _ : Fin n ↦ f))
        (_root_.RestrictScalars.span (R := R) (S := S)
          (TensorPower.Insertion.Exterior.repeatSet (R := S) (M := N) n)) := by
  rw [quotient_factor, LinearMap.ker_comp,
    _root_.RestrictScalars.ker_map,
    TensorPower.Insertion.Exterior.ker_eq_span_repeatSet]
  rfl

end Bundled

end RestrictScalars

end exteriorPower
