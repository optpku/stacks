/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w

namespace Algebra.TensorProduct

variable {F : Type u} {K : Type v} {L : Type w}
variable [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

/-- The canonical comparison `L`-algebra homomorphism from `K ⊗[F] L` to the product indexed by
`F`-algebra embeddings `K →ₐ[F] L`. -/
noncomputable def separableToPiAlgHom : K ⊗[F] L →ₐ[L] ((K →ₐ[F] L) → L) :=
  AlgHom.pi fun σ ↦
    (productLeftAlgHom (AlgHom.id L L) σ).comp (commRight F L K).symm.toAlgHom

/-- The separable tensor-product comparison sends a pure tensor to the function
`σ ↦ σ α * β`. -/
theorem separableToPiAlgHom_apply_tmul
    (α : K) (β : L) (σ : K →ₐ[F] L) :
    separableToPiAlgHom (α ⊗ₜ[F] β) σ = σ α * β := by
  simp [separableToPiAlgHom, mul_comm]

/-- Lemma 9.13.4 (Tag 0CKN): for a finite separable field extension `K/F` and an algebraically
closed extension field `L/F`, the separable tensor-product comparison is bijective. -/
theorem separableToPiAlgHom_bijective [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [IsAlgClosed L] :
    Function.Bijective (separableToPiAlgHom : K ⊗[F] L → (K →ₐ[F] L) → L) := by
  let n := Module.finrank F K
  let b := Module.finBasis F K
  have hEmbNat : Nat.card (K →ₐ[F] L) = n := by
    calc
      Nat.card (K →ₐ[F] L) = Field.finSepDegree F K := by
        symm
        simpa using (Field.finSepDegree_eq_of_isAlgClosed F K L)
      _ = Module.finrank F K := by
        simpa using (Field.finSepDegree_eq_finrank_of_isSeparable F K)
  let e : (K →ₐ[F] L) ≃ Fin n := Finite.equivFinOfCardEq hEmbNat
  let evBasis : (K →ₗ[F] L) →ₗ[L] Fin n → L :=
    { toFun := fun f j ↦ f (b j)
      map_add' := by
        intro f g
        ext j
        simp
      map_smul' := by
        intro c f
        ext j
        simp }
  let M : Matrix (Fin n) (Fin n) L := fun i j ↦
    evBasis (AlgHom.toLinearMap (e.symm i)) j
  let S : K ⊗[F] L ≃ₗ[L] Fin n → L :=
    (commRight F L K).symm.toLinearEquiv.trans (basis L b).equivFun
  let T : ((K →ₐ[F] L) → L) ≃ₗ[L] Fin n → L := LinearEquiv.funCongrLeft L L e.symm
  let f : (Fin n → L) →ₗ[L] Fin n → L :=
    T.toLinearMap.comp
      (((separableToPiAlgHom : K ⊗[F] L →ₐ[L] ((K →ₐ[F] L) → L)).toLinearMap).comp
        S.symm.toLinearMap)
  have hevBasis_inj : Function.Injective evBasis := by
    intro φ ψ hφψ
    ext x
    rw [← b.sum_repr x]
    simp_rw [map_sum, map_smul]
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact congrArg (fun z ↦ (b.repr x) i • z) (congrFun hφψ i)
  have hM_rows : LinearIndependent L M.row := by
    have hevBasis_ker : LinearMap.ker evBasis = ⊥ := LinearMap.ker_eq_bot.mpr hevBasis_inj
    change LinearIndependent L ((evBasis ∘ AlgHom.toLinearMap) ∘ e.symm)
    exact
      ((linearIndependent_algHom_toLinearMap F K L).map' evBasis hevBasis_ker).comp
        e.symm e.symm.injective
  have hM_unit : IsUnit M := (Matrix.linearIndependent_rows_iff_isUnit).mp hM_rows
  have hf_eq : f = Matrix.toLin' M := by
    apply LinearMap.toMatrix'.injective
    ext i j
    rw [LinearMap.toMatrix'_apply]
    simp [f, T, S, M, evBasis, separableToPiAlgHom_apply_tmul]
  have hf_inj : Function.Injective f := by
    rw [hf_eq]
    exact (Matrix.mulVec_injective_iff_isUnit).2 hM_unit
  have hf_surj : Function.Surjective f := by
    rw [hf_eq]
    exact (Matrix.mulVec_surjective_iff_isUnit).2 hM_unit
  constructor
  · intro x y hxy
    apply S.injective
    apply hf_inj
    simpa [f] using congrArg T hxy
  · intro g
    obtain ⟨v, hv⟩ := hf_surj (T g)
    refine ⟨S.symm v, ?_⟩
    apply T.injective
    simpa [f] using hv

/-- The canonical `L`-algebra equivalence from a finite separable tensor product to the product
of copies of the algebraically closed target indexed by embeddings. -/
noncomputable def separableToPiAlgEquiv [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [IsAlgClosed L] : K ⊗[F] L ≃ₐ[L] ((K →ₐ[F] L) → L) :=
  AlgEquiv.ofBijective separableToPiAlgHom separableToPiAlgHom_bijective

end Algebra.TensorProduct
