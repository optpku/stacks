module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localizations are algebra epimorphisms

The universal property of a localization makes its structure map an algebra
epimorphism. The theorem is stated for an arbitrary localization model; the
instance is reserved for the canonical `Localization M`, where the submonoid
is recoverable from the target type.

@stack 091P
-/

@[expose] public section

open TensorProduct
open scoped TensorProduct

universe u v

namespace Algebra.IsEpi

/-- Any localization model is an epimorphic algebra over its base. The
submonoid remains explicit because it cannot be inferred from an arbitrary
target algebra `A`. -/
@[stacks 091P "localization is an algebra epimorphism"]
theorem of_isLocalization {R : Type u} [CommSemiring R]
    (M : Submonoid R) (A : Type v) [CommSemiring A] [Algebra R A]
    [IsLocalization M A] :
    Algebra.IsEpi R A := by
  rw [Algebra.isEpi_iff_forall_one_tmul_eq]
  intro a
  have h :
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) =
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom := by
    apply IsLocalization.ringHom_ext M
    ext r
    change algebraMap R A r ⊗ₜ[R] 1 = 1 ⊗ₜ[R] algebraMap R A r
    simp only [Algebra.algebraMap_eq_smul_one, smul_tmul]
  exact (RingHom.congr_fun h a).symm

end Algebra.IsEpi

namespace Localization

/-- The canonical localization carries its algebra-epimorphism instance
without any local instance installation by downstream users. -/
@[stacks 091P "canonical localization is an algebra epimorphism"]
instance isEpi {R : Type u} [CommSemiring R] (M : Submonoid R) :
    Algebra.IsEpi R (Localization M) :=
  Algebra.IsEpi.of_isLocalization M (Localization M)

end Localization
