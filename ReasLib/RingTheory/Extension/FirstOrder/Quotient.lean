/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.FirstOrder
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.Tactic.CrossRefAttribute

/-!
# The First-Order Extension of a Quotient Ring

For an ideal `I` of a commutative ring `R`, this file packages the canonical
map `R ⧸ I ^ 2 → R ⧸ I` as an algebra extension.  Its kernel is Mathlib's
canonical ideal model `I.cotangentIdeal`, and its cotangent module is therefore
canonically equivalent to `I.Cotangent`.

The namespace keeps the generic words `factor`, `extension`, and `cotangentEquiv`
short while retaining the mathematical owner `Ideal.FirstOrder`.

@stack 04ED
-/

@[expose] public section

noncomputable section

open Algebra

namespace Ideal.FirstOrder

universe u z

variable {R : Type u} [CommRing R]

/-- The canonical algebra map `R ⧸ I ^ 2 → R ⧸ I`. -/
@[stacks 04ED "canonical quotient map"]
def factor (I : Ideal R) : (R ⧸ I ^ 2) →ₐ[R] R ⧸ I :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_self two_ne_zero)

/-- The canonical map `R ⧸ I ^ 2 → R ⧸ I` is surjective. -/
@[stacks 04ED "canonical quotient map is surjective"]
theorem factor_surjective (I : Ideal R) : Function.Surjective (factor I) := by
  exact Ideal.Quotient.factor_surjective (Ideal.pow_le_self two_ne_zero)

/-- The algebra extension represented by `R ⧸ I ^ 2 → R ⧸ I`. -/
@[stacks 04ED "canonical quotient extension"]
noncomputable def extension (I : Ideal R) : Algebra.Extension R (R ⧸ I) :=
  Algebra.Extension.ofSurjective (factor I) (factor_surjective I)

/-- The structure map of the canonical first-order extension is `factor I`. -/
@[simp, stacks 04ED "canonical quotient extension structure map"]
theorem extension_toAlgHom (I : Ideal R) :
    IsScalarTower.toAlgHom R (extension I).Ring (R ⧸ I) = factor I := by
  exact Algebra.Extension.toAlgHom_ofSurjective _ _

/-- The kernel of `R ⧸ I ^ 2 → R ⧸ I` is the canonical ideal copy of `I / I²`. -/
@[stacks 04ED "kernel of the canonical quotient extension"]
theorem factor_ker (I : Ideal R) :
    RingHom.ker (factor I).toRingHom = I.cotangentIdeal := by
  simpa [factor, Ideal.cotangentIdeal, Ideal.map_eq_submodule_map] using
    (Ideal.Quotient.factor_ker (Ideal.pow_le_self two_ne_zero) :
      RingHom.ker
          (Ideal.Quotient.factor (Ideal.pow_le_self two_ne_zero) :
            (R ⧸ I ^ 2) →+* R ⧸ I) =
        I.map (Ideal.Quotient.mk (I ^ 2)))

/-- The kernel of the canonical first-order extension is `I.cotangentIdeal`. -/
@[stacks 04ED "kernel of the canonical quotient extension"]
theorem extension_ker (I : Ideal R) :
    (extension I).ker = I.cotangentIdeal := by
  change RingHom.ker (factor I).toRingHom = I.cotangentIdeal
  exact factor_ker I

/-- The kernel of the canonical first-order extension, viewed over `R`, is
canonically `I / I²`. -/
@[stacks 04ED "kernel of the canonical quotient extension"]
noncomputable def kernelEquiv (I : Ideal R) :
    (extension I).ker ≃ₗ[R] I.Cotangent :=
  ((LinearEquiv.ofEq (extension I).ker I.cotangentIdeal
      (extension_ker I)).restrictScalars R).trans
    I.cotangentEquivIdeal.symm

private theorem algebraMap_eq_zero_of_mem_sq
    (I : Ideal R) {A : Type*} [CommRing A] [Algebra R A]
    (J : Ideal A) (hJ : J ^ 2 = ⊥) (f : R ⧸ I →ₐ[R] A ⧸ J)
    {x : R} (hx : x ∈ I ^ 2) :
    algebraMap R A x = 0 := by
  have hI : I ≤ J.comap (algebraMap R A) := by
    intro y hy
    change algebraMap R A y ∈ J
    have hy0 : (Ideal.Quotient.mk I y : R ⧸ I) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hy
    have hleft : f (Ideal.Quotient.mk I y) = 0 := by
      simpa only [map_zero] using congrArg f hy0
    have hcomm := f.commutes y
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.alg_map_eq] at hcomm
    rw [hcomm] at hleft
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [RingHom.comp_apply] using hleft)
  have hcomapSq :
      (J.comap (algebraMap R A)) ^ 2 ≤ RingHom.ker (algebraMap R A) := by
    intro z hz
    have hz' : z ∈ (J ^ 2).comap (algebraMap R A) :=
      Ideal.le_comap_pow (f := algebraMap R A) (K := J) 2 hz
    have : algebraMap R A z ∈ (⊥ : Ideal A) := by
      simpa [hJ] using hz'
    simpa [RingHom.mem_ker] using this
  have hsq : I ^ 2 ≤ RingHom.ker (algebraMap R A) :=
    (Ideal.pow_right_mono hI 2).trans hcomapSq
  simpa [RingHom.mem_ker] using hsq hx

/-- The canonical extension `R ⧸ I ^ 2 → R ⧸ I` is universal among
square-zero extensions of `R ⧸ I`. -/
@[stacks 04ED "universal first-order quotient extension"]
theorem isUniversal (I : Ideal R) :
    Algebra.Extension.FirstOrder.IsUniversal.{z} (extension I) := by
  refine ⟨?_, ?_⟩
  · rw [extension_ker]
    exact I.cotangentIdeal_square
  · intro A _ _ J hJ f
    rw [extension_toAlgHom]
    let lift : R ⧸ I ^ 2 →ₐ[R] A :=
      Ideal.Quotient.liftₐ (I ^ 2) (Algebra.ofId R A)
        (fun _ hx ↦ algebraMap_eq_zero_of_mem_sq I J hJ f hx)
    refine ⟨lift, ?_, ?_⟩
    · refine Ideal.Quotient.algHom_ext (R₁ := R) <|
        AlgHom.ext fun x ↦ (f.commutes x).symm
    · intro g _
      refine Ideal.Quotient.algHom_ext (R₁ := R) <| ?_
      calc
        g.comp (Ideal.Quotient.mkₐ R (I ^ 2)) = Algebra.ofId R A := by
          exact AlgHom.ext fun x ↦ g.commutes x
        _ = lift.comp (Ideal.Quotient.mkₐ R (I ^ 2)) := by
          symm
          exact Ideal.Quotient.liftₐ_comp (I ^ 2) (Algebra.ofId R A)
            (fun _ hx ↦ algebraMap_eq_zero_of_mem_sq I J hJ f hx)

/-- The cotangent module of the canonical first-order extension is `I / I²`.

This equivalence is constructed from `Ideal.cotangentEquivIdeal` and the
square-zero kernel equivalence; it does not choose a presentation or a basis. -/
@[stacks 04ED "cotangent module of the canonical quotient extension"]
noncomputable def cotangentEquiv (I : Ideal R) :
    (extension I).Cotangent ≃ₗ[R ⧸ I] I.Cotangent := by
  let P : Algebra.Extension R (R ⧸ I) := extension I
  have hker : P.ker = I.cotangentIdeal := by
    simpa [P] using extension_ker I
  have hsq : P.ker ^ 2 = ⊥ := by
    rw [hker]
    exact I.cotangentIdeal_square
  let e : I.Cotangent ≃ₗ[R] P.Cotangent :=
    I.cotangentEquivIdeal |>.trans
      ((LinearEquiv.ofEq I.cotangentIdeal P.ker hker.symm).restrictScalars R) |>.trans
      ((P.kerCotangentEquiv hsq).restrictScalars R)
  exact (e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective).symm

/-- The cotangent comparison sends a kernel generator to its canonical class
in `I / I²`. -/
@[simp, stacks 04ED "cotangent comparison on kernel generators"]
theorem cotangentEquiv_mk (I : Ideal R) (x : (extension I).ker) :
    cotangentEquiv I (Algebra.Extension.Cotangent.mk x) = kernelEquiv I x := by
  have hsq : (extension I).ker ^ 2 = ⊥ := by
    rw [extension_ker]
    exact I.cotangentIdeal_square
  simp [cotangentEquiv, kernelEquiv]
  congr 2
  exact (extension I).kerCotangentEquiv_symm_mk hsq x

/-- The inverse cotangent comparison represents a class in `I / I²` by the
corresponding kernel generator. -/
@[simp, stacks 04ED "inverse cotangent comparison on classes"]
theorem cotangentEquiv_symm_apply (I : Ideal R) (x : I.Cotangent) :
    (cotangentEquiv I).symm x =
      Algebra.Extension.Cotangent.mk ((kernelEquiv I).symm x) := by
  apply (cotangentEquiv I).injective
  simp

end Ideal.FirstOrder
