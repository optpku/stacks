module

public import ReasLib.LinearAlgebra.Quotient.Map
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear maps on quotients by ideal multiples

This file owns the canonical map induced by a linear map after quotienting its source and target by
the multiples of the same ideal.
-/

@[expose] public section

universe u v w x

namespace LinearMap

section QuotientMap

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']
variable {M'' : Type x} [AddCommGroup M''] [Module R M'']

/-- The map induced by `f : M →ₗ[R] M'` on the quotients by `I M` and `I M'`. -/
@[stacks 00DV "linear maps on ideal quotients"]
abbrev quotientMapByIdeal (f : M →ₗ[R] M') (I : Ideal R) :
    M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R] M' ⧸ (I • (⊤ : Submodule R M')) :=
  (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R M')) f
    (Submodule.smul_top_le_comap_smul_top I f)

/-- The induced quotient map sends the class of `x` to the class of `f x`. -/
@[simp]
theorem quotientMapByIdeal_apply_mk (f : M →ₗ[R] M') (I : Ideal R) (x : M) :
    f.quotientMapByIdeal I (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) :=
  rfl

/-! ### Functoriality -/

/-- Quotienting a linear map by ideal multiples preserves identity maps. -/
@[simp]
theorem quotientMapByIdeal_id (I : Ideal R) :
    (LinearMap.id : M →ₗ[R] M).quotientMapByIdeal I = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x⟩
  rfl

/-- Quotienting by ideal multiples commutes with composition of linear maps. -/
theorem quotientMapByIdeal_comp (f : M →ₗ[R] M') (g : M' →ₗ[R] M'') (I : Ideal R) :
    (g.comp f).quotientMapByIdeal I =
      (g.quotientMapByIdeal I).comp (f.quotientMapByIdeal I) := by
  apply LinearMap.ext
  rintro ⟨x⟩
  rfl

/-- The map induced by `f` on ideal quotients is injective exactly when the preimage of the
target ideal multiple is contained in the source ideal multiple. -/
@[stacks 00DV "quotient-map injectivity criterion"]
theorem quotientMapByIdeal_injective_iff_comap_smul_top
    (I : Ideal R) (f : M →ₗ[R] M') :
    Function.Injective (f.quotientMapByIdeal I) ↔
      Submodule.comap f (I • (⊤ : Submodule R M')) ≤
        I • (⊤ : Submodule R M) :=
  Submodule.mapQ_injective_iff _ _ _ _

/-- Pointwise form of `quotientMapByIdeal_injective_iff_comap_smul_top`, useful when a proof
already supplies membership of an image in the target ideal multiple. -/
@[stacks 00DV "pointwise quotient-map injectivity criterion"]
theorem quotientMapByIdeal_injective_iff_mem_smul
    (I : Ideal R) (f : M →ₗ[R] M') :
    Function.Injective (f.quotientMapByIdeal I) ↔
      ∀ z, f z ∈ I • (⊤ : Submodule R M') → z ∈ I • (⊤ : Submodule R M) := by
  rw [quotientMapByIdeal_injective_iff_comap_smul_top]
  rfl

/-- The map induced by `f` after quotienting by the `n`-th power of `I`. -/
abbrev quotientMapByIdealPower (f : M →ₗ[R] M') (I : Ideal R) (n : ℕ+) :
    M ⧸ (I ^ (n : ℕ) • (⊤ : Submodule R M)) →ₗ[R]
      M' ⧸ (I ^ (n : ℕ) • (⊤ : Submodule R M')) :=
  f.quotientMapByIdeal (I ^ (n : ℕ))

/-- The quotient map by an ideal power sends the class of `x` to the class of `f x`. -/
@[simp]
theorem quotientMapByIdealPower_apply_mk (f : M →ₗ[R] M') (I : Ideal R) (n : ℕ+) (x : M) :
    f.quotientMapByIdealPower I n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f x) :=
  quotientMapByIdeal_apply_mk f (I ^ (n : ℕ)) x

/-- Quotienting by an ideal power preserves identity maps. -/
@[simp]
theorem quotientMapByIdealPower_id (I : Ideal R) (n : ℕ+) :
    (LinearMap.id : M →ₗ[R] M).quotientMapByIdealPower I n = LinearMap.id :=
  quotientMapByIdeal_id (I ^ (n : ℕ))

/-- Quotienting by an ideal power commutes with composition of linear maps. -/
theorem quotientMapByIdealPower_comp (f : M →ₗ[R] M') (g : M' →ₗ[R] M'')
    (I : Ideal R) (n : ℕ+) :
    (g.comp f).quotientMapByIdealPower I n =
      (g.quotientMapByIdealPower I n).comp (f.quotientMapByIdealPower I n) :=
  quotientMapByIdeal_comp f g (I ^ (n : ℕ))

end QuotientMap

section Surjectivity

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

/-- The map induced by `f` modulo an ideal is surjective exactly when the range of `f` together
with the ideal multiple of the target generates the target. -/
@[stacks 00DV "quotient-map generation criterion"]
theorem quotientMapByIdeal_surjective_iff (f : M →ₗ[R] M') (I : Ideal R) :
    Function.Surjective (f.quotientMapByIdeal I) ↔
      f.range ⊔ I • (⊤ : Submodule R M') = ⊤ := by
  rw [← LinearMap.range_eq_top, Submodule.range_mapQ,
    Submodule.map_mkQ_eq_top, sup_comm]

end Surjectivity

section Annihilator

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

/-- A linear map whose kernel and cokernel are annihilated by a positive power of an ideal. -/
@[stacks 0888]
def HasKernelCokernelAnnihilatedByPower (I : Ideal R) (f : M →ₗ[R] M') : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    I ^ n ≤ Module.annihilator R f.ker ∧
      I ^ n ≤ Module.annihilator R (M' ⧸ f.range)

/-- Unfold `HasKernelCokernelAnnihilatedByPower` into a common positive annihilating exponent. -/
theorem hasKernelCokernelAnnihilatedByPower_iff (I : Ideal R) (f : M →ₗ[R] M') :
    HasKernelCokernelAnnihilatedByPower I f ↔
      ∃ n : ℕ, 1 ≤ n ∧
        I ^ n ≤ Module.annihilator R f.ker ∧
          I ^ n ≤ Module.annihilator R (M' ⧸ f.range) :=
  Iff.rfl

/-- Every positive ideal-power quotient of a linear map has kernel and cokernel annihilated by
one common positive power of a second ideal. -/
@[stacks 0888]
def QuotientMapsHaveKernelCokernelAnnihilatedByPower
    (I K : Ideal R) (f : M →ₗ[R] M') : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ+,
    K ^ t ≤ Module.annihilator R (f.quotientMapByIdealPower I n).ker ∧
      K ^ t ≤ Module.annihilator R
        ((M' ⧸ I ^ (n : ℕ) • (⊤ : Submodule R M')) ⧸
          (f.quotientMapByIdealPower I n).range)

/-- Unfold the uniform annihilation condition for all positive ideal-power quotient maps. -/
theorem quotientMapsHaveKernelCokernelAnnihilatedByPower_iff
    (I K : Ideal R) (f : M →ₗ[R] M') :
    QuotientMapsHaveKernelCokernelAnnihilatedByPower I K f ↔
      ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ+,
        K ^ t ≤ Module.annihilator R (f.quotientMapByIdealPower I n).ker ∧
          K ^ t ≤ Module.annihilator R
            ((M' ⧸ I ^ (n : ℕ) • (⊤ : Submodule R M')) ⧸
              (f.quotientMapByIdealPower I n).range) :=
  Iff.rfl

/-- If the kernel and cokernel of `f` are killed by `I ^ n`, then the kernel and cokernel after
quotienting source and target by any ideal `J` are killed by `I ^ (2 * n)`. -/
@[stacks 0888]
theorem quotientMapByIdeal_kernel_cokernel_annihilated
    (I J : Ideal R) (f : M →ₗ[R] M') {n : ℕ}
    (hker : I ^ n ≤ Module.annihilator R f.ker)
    (hcoker : I ^ n ≤ Module.annihilator R (M' ⧸ f.range)) :
    I ^ (2 * n) ≤ Module.annihilator R (f.quotientMapByIdeal J).ker ∧
      I ^ (2 * n) ≤
        Module.annihilator R
          ((M' ⧸ J • (⊤ : Submodule R M')) ⧸ (f.quotientMapByIdeal J).range) := by
  have hRange : I ^ n • (⊤ : Submodule R M') ≤ f.range := by
    refine Submodule.smul_le.mpr ?_
    intro a ha y _
    have hay :=
      Module.mem_annihilator.mp (hcoker ha) (Submodule.Quotient.mk y)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hay
    exact hay
  have hRangeJ :
      I ^ n • (J • (⊤ : Submodule R M')) ≤
        (J • (⊤ : Submodule R M)).map f := by
    calc
      I ^ n • (J • (⊤ : Submodule R M')) =
          J • (I ^ n • (⊤ : Submodule R M')) := by
            rw [← mul_smul, mul_comm, mul_smul]
      _ ≤ J • f.range := Submodule.smul_le.mpr fun a ha y hy ↦
        Submodule.smul_mem_smul ha (hRange hy)
      _ = (J • (⊤ : Submodule R M)).map f := by
        rw [Submodule.map_smul'', Submodule.map_top]
  have hkernel :
      I ^ (2 * n) ≤ Module.annihilator R (f.quotientMapByIdeal J).ker := by
    rw [show I ^ (2 * n) = I ^ n * I ^ n by rw [two_mul, pow_add],
      Submodule.le_annihilator_iff, mul_smul]
    apply le_antisymm ?_ bot_le
    refine Submodule.smul_le.mpr ?_
    intro a ha y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro b hb x hx
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
          rw [Submodule.mem_bot]
          have hfx : f x ∈ J • (⊤ : Submodule R M') := by
            change f.quotientMapByIdeal J (Submodule.Quotient.mk x) = 0 at hx
            rw [quotientMapByIdeal_apply_mk, Submodule.Quotient.mk_eq_zero] at hx
            exact hx
          rcases hRangeJ (Submodule.smul_mem_smul hb hfx) with ⟨z, hz, hzmap⟩
          have hd : b • x - z ∈ f.ker := by
            change f (b • x - z) = 0
            rw [map_sub, map_smul, hzmap, sub_self]
          have had := congrArg Subtype.val
            (Module.mem_annihilator.mp (hker ha) ⟨b • x - z, hd⟩)
          change a • (b • x - z) = 0 at had
          rw [smul_sub, sub_eq_zero] at had
          rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
            Submodule.Quotient.mk_eq_zero, had]
          exact (J • (⊤ : Submodule R M)).smul_mem a hz
    · intro x y hx hy
      rw [smul_add]
      exact add_mem hx hy
  refine ⟨hkernel, ?_⟩
  have hRangeQuotient :
      I ^ n • (⊤ : Submodule R (M' ⧸ J • (⊤ : Submodule R M'))) ≤
        (f.quotientMapByIdeal J).range := by
    refine Submodule.smul_le.mpr ?_
    intro a ha y _
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
        rcases hRange (Submodule.smul_mem_smul ha (Submodule.mem_top)) with ⟨x, hx⟩
        refine ⟨Submodule.Quotient.mk x, ?_⟩
        rw [quotientMapByIdeal_apply_mk, ← Submodule.Quotient.mk_smul, hx]
  have hcokerQuotient :
      I ^ n ≤ Module.annihilator R
        ((M' ⧸ J • (⊤ : Submodule R M')) ⧸ (f.quotientMapByIdeal J).range) := by
    intro a ha
    rw [Module.mem_annihilator]
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact hRangeQuotient (Submodule.smul_mem_smul ha (Submodule.mem_top))
  exact (Ideal.pow_le_pow_right (by simpa [two_mul] using Nat.le_add_right n n)).trans
    hcokerQuotient

/-- For complete source and target modules, kernel-and-cokernel annihilation of a linear map is
equivalent to uniform annihilation for all of its positive ideal-power quotient maps. -/
@[stacks 0888]
theorem hasKernelCokernelAnnihilatedByPower_iff_quotientMaps
    (I K : Ideal R) (f : M →ₗ[R] M')
    [IsAdicComplete I M] [IsAdicComplete I M'] :
    HasKernelCokernelAnnihilatedByPower K f ↔
      QuotientMapsHaveKernelCokernelAnnihilatedByPower I K f := sorry

end Annihilator

end LinearMap
