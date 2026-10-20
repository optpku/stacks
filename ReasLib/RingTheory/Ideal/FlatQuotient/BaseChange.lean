module

public import ReasLib.RingTheory.Ideal.FlatQuotient
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for flat quotient ideals

The quotient factorization and tensor comparisons used by the Artinian flat-quotient criterion are
generic maps attached to an ideal killed by an algebra map.  They are kept below the
`Ideal.FlatQuotient` namespace so source chapters can use short, mathematically layered names.

@stack 0525
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Ideal.FlatQuotient

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {R' : Type w} [CommRing R'] [Algebra R R']

/-- The vanishing image of `J` makes every element of `J` vanish in the target algebra. -/
theorem mapMemZero {J : Ideal R}
    (hmap : J.map (algebraMap R R') = ⊥) {a : R} (ha : a ∈ J) :
    (algebraMap R R') a = 0 := sorry

/-- Construct the quotient factorization from an explicit elementwise vanishing proof. -/
@[stacks 0525 "explicit quotient factorization"]
noncomputable def factorAlgHomOf {J : Ideal R}
    (hzero : ∀ a, a ∈ J → (algebraMap R R') a = 0) :
    R ⧸ J →ₐ[R] R' :=
  Ideal.Quotient.liftₐ (R₁ := R) (I := J) (Algebra.ofId R R')
    (fun a ha ↦ hzero a ha)

/-- The canonical `R ⧸ J →ₐ[R] R'` when the image of `J` in `R'` is zero. -/
@[stacks 0525 "quotient factorization through a vanishing ideal"]
noncomputable def factorAlgHom {J : Ideal R}
    (hmap : J.map (algebraMap R R') = ⊥) :
    R ⧸ J →ₐ[R] R' :=
  factorAlgHomOf (R := R) (R' := R')
    (fun _ ha ↦ mapMemZero (R := R) (R' := R') hmap ha)

/-- The quotient by the kernel of `R → R'` has its canonical comparison algebra hom to `R'`. -/
@[stacks 0525 "kernel quotient comparison map"]
noncomputable def kernelAlgHom :
    R ⧸ RingHom.ker (algebraMap R R') →ₐ[R] R' :=
  Ideal.kerLiftAlg (Algebra.ofId R R')

/-- The ideal action on `R' ⊗[R] M` vanishes when the ideal image is zero. -/
theorem mapSmulTop_eq_bot {J : Ideal R}
    (hmap : J.map (algebraMap R R') = ⊥) :
    J.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M)) = ⊥ := sorry

/-- Compare tensoring the quotient module over `R ⧸ J` and over `R`, after an algebra structure
`R ⧸ J → R'` has been supplied. -/
@[stacks 0525 "factor-ring tensor comparison"]
noncomputable def factorTensor {J : Ideal R}
    [Algebra (R ⧸ J) R'] [IsScalarTower R (R ⧸ J) R'] :
    (R' ⊗[R ⧸ J] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R']
      (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) :=
  -- Pin the quotient's surjective scalar comparison locally: this is the canonical
  -- `CompatibleSMul` needed by `lidOfCompatibleSMul`, and is not an ambient choice.
  letI :
      TensorProduct.CompatibleSMul R (R ⧸ J) (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))) :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := R) (A := R ⧸ J) (M := R ⧸ J) (N := M ⧸ (J • (⊤ : Submodule R M)))
      Ideal.Quotient.mk_surjective
  let eLid :
      ((R ⧸ J) ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R ⧸ J]
        (M ⧸ (J • (⊤ : Submodule R M))) :=
    TensorProduct.lidOfCompatibleSMul R (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') eLid.symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ J) R' R'
      (M ⧸ (J • (⊤ : Submodule R M))))

/-- The quotient/tensor comparison with an explicit proof that the induced ideal action is zero.
The explicit proof parameter keeps the non-Prop data independent of the theorem proving
`mapSmulTop_eq_bot`. -/
@[stacks 0525 "explicit base-change tensor comparison"]
noncomputable def baseTensorOf {J : Ideal R}
    (hzero : J.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M)) = ⊥) :
    (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R'] (R' ⊗[R] M) :=
  let eBot :
      (R' ⊗[R] M) ≃ₗ[R']
        ((R' ⊗[R] M) ⧸
          J.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M))) :=
    ((J.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M))).quotEquivOfEqBot hzero).symm
  let eTensorQuot :
      (((R' ⊗[R] M) ⧸
          J.map (algebraMap R R') • (⊤ : Submodule R' (R' ⊗[R] M)))) ≃ₗ[R']
        (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) :=
    TensorProduct.tensorQuotMapSMulEquivTensorQuot (S := R') (M := M) J
  (eBot.trans eTensorQuot).symm

/-- The canonical quotient/tensor comparison when the image of `J` is zero. -/
@[stacks 0525 "base-change tensor comparison for a vanishing ideal"]
noncomputable def baseTensor {J : Ideal R}
    (hmap : J.map (algebraMap R R') = ⊥) :
    (R' ⊗[R] (M ⧸ (J • (⊤ : Submodule R M)))) ≃ₗ[R'] (R' ⊗[R] M) :=
  baseTensorOf (R := R) (M := M) (R' := R')
    (mapSmulTop_eq_bot (R := R) (M := M) (R' := R') hmap)

end Ideal.FlatQuotient

end
