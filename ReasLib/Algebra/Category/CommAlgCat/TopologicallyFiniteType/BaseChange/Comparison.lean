/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.InverseLimit
public import ReasLib.RingTheory.AdicAlgebraSystem.BaseChange
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.BaseChange.Maps

/-!
# Comparison of systems and completed base change

A ring map carrying a positive power of the first ideal into the second induces
base change of adic systems and completed tensor products. The stagewise tensor
and completion comparisons give a natural isomorphism commuting with passage
to quotient systems, and inverse limits transport this comparison when both
ideals are finitely generated.
-/

@[expose] public section

open CategoryTheory
open Algebra.TopologicallyFiniteType
open scoped TensorProduct

noncomputable section

universe u

variable {A1 A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2]

namespace CommAlgCat.TopologicallyFiniteType

open AdicAlgebraSystem (baseChangeHom stretchIndex tensorOverIncludeLeft
  tensorOverIncludeRight tensorOverLift stageAlgebraMap)

/-- The systems-base-change form of the completed-base-change containment. -/
private theorem map_pow_le_of_map_pow (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) :
    Ideal.map (algebraMap A1 A2) (I1 ^ c) ≤ I2 := by
  simpa only [Ideal.map_pow] using hI

/-- The extended power `I1 ^ (c * n) B` lands in the comap of `I2 ^ n` along
`includeLeftToCompletion`. -/
private theorem stageCompareLeft_le_comap (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2)
    (B : Type u) [CommRing B] [Algebra A1 B] (n : ℕ+) :
    (I1 ^ (stretchIndex hc n : ℕ)).map (algebraMap A1 B) ≤
      ((I2 ^ (n : ℕ)).map (algebraMap A2 (completedBaseChange A1 I2 B))).comap
        (includeLeftToCompletion I2 B) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, includeLeftToCompletion_comp,
    ← Ideal.map_map]
  exact Ideal.map_mono (AdicAlgebraSystem.map_pow_le (algebraMap A1 A2) I1 I2 hc
    (by exact map_pow_le_of_map_pow I1 I2 hI) n)

/-- The stage map `B ⧸ I1 ^ (c * n) B → (B ⊗[A1] A2)^∧ ⧸ I2 ^ n (B ⊗[A1] A2)^∧`
induced by `includeLeftToCompletion`. -/
def stageCompareLeftHom (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    ((toAdicSystem I1).obj B).obj.right.stage (stretchIndex hc n) →+*
      ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj.right.stage n :=
  Ideal.quotientMap
    ((I2 ^ (n : ℕ)).map (algebraMap A2 ((baseChange I1 I2 hc hI hI2).obj B).obj))
    (includeLeftToCompletion I2 B.obj)
    (by exact stageCompareLeft_le_comap I1 I2 hc hI B.obj n)

/-- `stageCompareLeftHom` is the quotient of `includeLeftToCompletion`. -/
theorem stageCompareLeftHom_mk (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+)
    (x : B.obj) :
    stageCompareLeftHom I1 I2 hc hI hI2 B n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (includeLeftToCompletion I2 B.obj x) := by
  rfl

private theorem tensorOverLift_comp_includeLeft {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (f : R →+* A) (g : R →+* B) (hA : A →+* C) (hB : B →+* C)
    (hfg : hA.comp f = hB.comp g) :
    (tensorOverLift f g hA hB hfg).comp (tensorOverIncludeLeft f g) = hA := by
  -- These local algebra structures are the supplied ring homomorphisms.
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (hA.comp f).toAlgebra
  exact congrArg AlgHom.toRingHom
    (Algebra.TensorProduct.lift_comp_includeLeft
      ({ hA with commutes' := fun _ ↦ rfl } : A →ₐ[R] C)
      ({ hB with commutes' := fun r ↦ (RingHom.congr_fun hfg r).symm } : B →ₐ[R] C)
      (fun _ _ ↦ Commute.all _ _))

private theorem tensorOverLift_comp_includeRight {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (f : R →+* A) (g : R →+* B) (hA : A →+* C) (hB : B →+* C)
    (hfg : hA.comp f = hB.comp g) :
    (tensorOverLift f g hA hB hfg).comp (tensorOverIncludeRight f g) = hB := by
  -- These local algebra structures are the supplied ring homomorphisms.
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (hA.comp f).toAlgebra
  exact congrArg AlgHom.toRingHom
    (Algebra.TensorProduct.lift_comp_includeRight'
      ({ hA with commutes' := fun _ ↦ rfl } : A →ₐ[R] C)
      ({ hB with commutes' := fun r ↦ (RingHom.congr_fun hfg r).symm } : B →ₐ[R] C)
      (fun _ _ ↦ Commute.all _ _))

private theorem tensorOver_hom_ext {R A B C : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (f : R →+* A) (g : R →+* B) {h k : AdicAlgebraSystem.tensorOver f g →+* C}
    (hl : h.comp (tensorOverIncludeLeft f g) = k.comp (tensorOverIncludeLeft f g))
    (hr : h.comp (tensorOverIncludeRight f g) = k.comp (tensorOverIncludeRight f g)) :
    h = k := by
  -- Extensionality uses the algebra structures of the two supplied scalar maps.
  letI := f.toAlgebra
  letI := g.toAlgebra
  exact Algebra.TensorProduct.ringHom_ext hl hr

private theorem tensorOverMap_comp_includeLeft {R A B A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (f : R →+* A) (g : R →+* B) (f' : R →+* A') (g' : R →+* B')
    (hA : A →+* A') (hB : B →+* B')
    (hf : hA.comp f = f') (hg : hB.comp g = g') :
    (AdicAlgebraSystem.tensorOverMap f g f' g' hA hB hf hg).comp
        (tensorOverIncludeLeft f g) = (tensorOverIncludeLeft f' g').comp hA := by
  -- Both tensors use the algebra structures of the four supplied scalar maps.
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := f'.toAlgebra
  letI := g'.toAlgebra
  exact congrArg AlgHom.toRingHom
    (Algebra.TensorProduct.map_comp_includeLeft
      ({ hA with commutes' := fun r ↦ RingHom.congr_fun hf r } : A →ₐ[R] A')
      ({ hB with commutes' := fun r ↦ RingHom.congr_fun hg r } : B →ₐ[R] B'))

private theorem tensorOverMap_comp_includeRight {R A B A' B' : Type u}
    [CommRing R] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (f : R →+* A) (g : R →+* B) (f' : R →+* A') (g' : R →+* B')
    (hA : A →+* A') (hB : B →+* B')
    (hf : hA.comp f = f') (hg : hB.comp g = g') :
    (AdicAlgebraSystem.tensorOverMap f g f' g' hA hB hf hg).comp
        (tensorOverIncludeRight f g) = (tensorOverIncludeRight f' g').comp hB := by
  -- Both tensors use the algebra structures of the four supplied scalar maps.
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := f'.toAlgebra
  letI := g'.toAlgebra
  exact congrArg AlgHom.toRingHom
    (Algebra.TensorProduct.map_comp_includeRight
      ({ hA with commutes' := fun r ↦ RingHom.congr_fun hf r } : A →ₐ[R] A')
      ({ hB with commutes' := fun r ↦ RingHom.congr_fun hg r } : B →ₐ[R] B'))

/-- The stage comparison homomorphism from the systems tensor
`B (c * n) ⊗[A1 ⧸ I1 ^ (c * n)] (A2 ⧸ I2 ^ n)` to the adic quotient of the
completed tensor. -/
def stageCompareHom (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    AdicAlgebraSystem.baseChangeStage (algebraMap A1 A2) I1 I2 hc
        (by exact map_pow_le_of_map_pow I1 I2 hI) ((toAdicSystem I1).obj B).obj n →+*
      ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj.right.stage n :=
  tensorOverLift
    (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n))
    (baseChangeHom (algebraMap A1 A2) I1 I2 hc (by exact map_pow_le_of_map_pow I1 I2 hI) n)
    (stageCompareLeftHom I1 I2 hc hI hI2 B n)
    (stageAlgebraMap I2 ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj n)
    (by
      apply Ideal.Quotient.ringHom_ext
      ext a
      exact congrArg (Ideal.Quotient.mk _)
        (RingHom.congr_fun (includeLeftToCompletion_comp I2 B.obj) a))

/-- The left inclusion into the systems tensor is sent to `stageCompareLeftHom`. -/
theorem stageCompareHom_includeLeft (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    (stageCompareHom I1 I2 hc hI hI2 B n).comp
      (tensorOverIncludeLeft
        (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n))
        (baseChangeHom (algebraMap A1 A2) I1 I2 hc (by exact map_pow_le_of_map_pow I1 I2 hI) n)) =
      stageCompareLeftHom I1 I2 hc hI hI2 B n := by
  exact tensorOverLift_comp_includeLeft _ _ _ _ _

/-- The right inclusion into the systems tensor is sent to the stage structure
map of the completed system. -/
theorem stageCompareHom_includeRight (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    (stageCompareHom I1 I2 hc hI hI2 B n).comp
      (tensorOverIncludeRight
        (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n))
        (baseChangeHom (algebraMap A1 A2) I1 I2 hc (by exact map_pow_le_of_map_pow I1 I2 hI) n)) =
      stageAlgebraMap I2
        ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj n := by
  exact tensorOverLift_comp_includeRight _ _ _ _ _

private def quotientTensorOverEquiv {R B D : Type u}
    [CommRing R] [CommRing B] [CommRing D] [Algebra R B] [Algebra R D]
    (I : Ideal R) (g : R ⧸ I →+* D) (hg : g.comp (Ideal.Quotient.mk I) = algebraMap R D) :
    AdicAlgebraSystem.tensorOver (Ideal.quotientMap (I.map (algebraMap R B))
        (algebraMap R B) Ideal.le_comap_map) g ≃+*
      B ⊗[R] D := by
  let f := Ideal.quotientMap (I.map (algebraMap R B)) (algebraMap R B) Ideal.le_comap_map
  let h : B ⧸ I.map (algebraMap R B) →+* B ⊗[R] D :=
    Ideal.Quotient.lift _ Algebra.TensorProduct.includeLeftRingHom (by
      intro b hb
      have hle : I.map (algebraMap R B) ≤
          RingHom.ker (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] D) := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        change Algebra.TensorProduct.includeLeftRingHom (algebraMap R B a) = 0
        have he := RingHom.congr_fun
          (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := R) (A := B) (B := D)) a
        dsimp only [RingHom.comp_apply] at he
        rw [he]
        rw [← hg]
        change Algebra.TensorProduct.includeRight (g (Ideal.Quotient.mk I a)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]
      exact hle hb)
  let t := tensorOverLift f g h Algebra.TensorProduct.includeRight.toRingHom (by
    apply Ideal.Quotient.ringHom_ext
    ext a
    exact (RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := R) (A := B) (B := D)) a).trans
      (congrArg (Algebra.TensorProduct.includeRight (R := R) (A := B))
        (RingHom.congr_fun hg a).symm))
  let left := (tensorOverIncludeLeft f g).comp (Ideal.Quotient.mk _)
  have hj : left.comp (algebraMap R B) = (tensorOverIncludeRight f g).comp (algebraMap R D) := by
      -- Local instance justification (noncanonical choice): balancing uses the explicit quotient structure map f.
      letI := f.toAlgebra
      -- Local instance justification (noncanonical choice): balancing uses the supplied scalar map g.
      letI := g.toAlgebra
      ext a
      have he := RingHom.congr_fun
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := R ⧸ I)
          (A := B ⧸ I.map (algebraMap R B)) (B := D)) (Ideal.Quotient.mk I a)
      exact he.trans (congrArg (tensorOverIncludeRight f g) (RingHom.congr_fun hg a))
  -- Local instance justification (noncanonical choice): the target R-algebra is determined by the supplied left scalar map.
  letI := (left.comp (algebraMap R B)).toAlgebra
  let j : B ⊗[R] D →+* AdicAlgebraSystem.tensorOver f g :=
    (Algebra.TensorProduct.lift
      ({ left with commutes' := fun _ ↦ rfl } : B →ₐ[R] _)
      ({ tensorOverIncludeRight f g with
        commutes' := fun r ↦ (RingHom.congr_fun hj r).symm } : D →ₐ[R] _)
      (fun _ _ ↦ Commute.all _ _)).toRingHom
  have jl (b : B) : j (b ⊗ₜ[R] (1 : D)) = tensorOverIncludeLeft f g (Ideal.Quotient.mk _ b) := by
    change tensorOverIncludeLeft f g (Ideal.Quotient.mk _ b) * tensorOverIncludeRight f g 1 = _
    rw [map_one, mul_one]
  have jr (d : D) : j ((1 : B) ⊗ₜ[R] d) = tensorOverIncludeRight f g d := by
    change tensorOverIncludeLeft f g (Ideal.Quotient.mk _ 1) * tensorOverIncludeRight f g d = _
    rw [map_one, map_one, one_mul]
  have tl (b : B ⧸ I.map (algebraMap R B)) : t (tensorOverIncludeLeft f g b) = h b := by
    change h b * Algebra.TensorProduct.includeRight (1 : D) = _
    rw [map_one, mul_one]
  have tr (d : D) : t (tensorOverIncludeRight f g d) = Algebra.TensorProduct.includeRight d := by
    change h 1 * Algebra.TensorProduct.includeRight d = _
    rw [map_one, one_mul]
  refine RingEquiv.ofRingHom t j ?_ ?_
  · apply Algebra.TensorProduct.ringHom_ext
    · ext b
      change t (j (b ⊗ₜ[R] (1 : D))) = b ⊗ₜ[R] (1 : D)
      rw [jl, tl]
      rfl
    · ext d
      change t (j ((1 : B) ⊗ₜ[R] d)) = (1 : B) ⊗ₜ[R] d
      rw [jr, tr]
      rfl
  ·
    -- Local instance justification (noncanonical choice): tensor extensionality uses the explicit scalar map f.
    letI := f.toAlgebra
    -- Local instance justification (noncanonical choice): tensor extensionality uses the supplied scalar map g.
    letI := g.toAlgebra
    apply Algebra.TensorProduct.ringHom_ext
    · apply Ideal.Quotient.ringHom_ext
      ext b
      change j (t (tensorOverIncludeLeft f g (Ideal.Quotient.mk _ b))) = _
      rw [tl]
      exact jl b
    · ext d
      change j (t (tensorOverIncludeRight f g d)) = _
      rw [tr]
      exact jr d

private theorem quotientTensorOverEquiv_left {R B D : Type u}
    [CommRing R] [CommRing B] [CommRing D] [Algebra R B] [Algebra R D]
    (I : Ideal R) (g : R ⧸ I →+* D) (hg : g.comp (Ideal.Quotient.mk I) = algebraMap R D) (b : B) :
    quotientTensorOverEquiv I g hg
      (tensorOverIncludeLeft (Ideal.quotientMap (I.map (algebraMap R B))
        (algebraMap R B) Ideal.le_comap_map) g (Ideal.Quotient.mk _ b)) = b ⊗ₜ[R] (1 : D) := by
  change Algebra.TensorProduct.includeLeftRingHom b * Algebra.TensorProduct.includeRight (1 : D) = _
  rw [map_one, mul_one]
  rfl

private theorem quotientTensorOverEquiv_right {R B D : Type u}
    [CommRing R] [CommRing B] [CommRing D] [Algebra R B] [Algebra R D]
    (I : Ideal R) (g : R ⧸ I →+* D) (hg : g.comp (Ideal.Quotient.mk I) = algebraMap R D) (d : D) :
    quotientTensorOverEquiv (B := B) I g hg
      (tensorOverIncludeRight (Ideal.quotientMap (I.map (algebraMap R B))
        (algebraMap R B) Ideal.le_comap_map) g d) = (1 : B) ⊗ₜ[R] d := by
  have hz : ∀ b ∈ I.map (algebraMap R B),
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] D) b = 0 := by
    have hle : I.map (algebraMap R B) ≤
        RingHom.ker (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] D) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change Algebra.TensorProduct.includeLeftRingHom (algebraMap R B a) = 0
      have he := RingHom.congr_fun
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := R) (A := B) (B := D)) a
      dsimp only [RingHom.comp_apply] at he
      rw [he, ← hg]
      change Algebra.TensorProduct.includeRight (g (Ideal.Quotient.mk I a)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]
    exact fun b hb ↦ hle hb
  change (Ideal.Quotient.lift (I.map (algebraMap R B))
    (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] D) hz) 1 *
      Algebra.TensorProduct.includeRight d = _
  rw [map_one, one_mul]
  rfl

private def completionQuotientEquiv {T : Type u} [CommRing T]
    (J : Ideal T) (hJ : J.FG) (n : ℕ) :
    T ⧸ J ^ n ≃+* AdicCompletion J T ⧸ (J ^ n).map (algebraMap T (AdicCompletion J T)) := by
  let f := (AdicCompletion.evalₐ J n).toRingHom
  have hk : RingHom.ker f = (J ^ n).map (algebraMap T (AdicCompletion J T)) := by
    ext x
    change AdicCompletion.evalₐ J n x = 0 ↔ _
    have h : (J ^ n • ⊤ : Ideal T) = J ^ n := by simp
    rw [show AdicCompletion.evalₐ J n x = 0 ↔ AdicCompletion.eval J T n x = 0 from
      (map_eq_zero_iff (Ideal.quotientEquivAlgOfEq T h)
        (Ideal.quotientEquivAlgOfEq T h).injective).trans Iff.rfl]
    change x ∈ (AdicCompletion.eval J T n).ker ↔ _
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval hJ]
    rw [Ideal.smul_top_eq_map]
    rfl
  let e := RingHom.quotientKerEquivOfSurjective (AdicCompletion.surjective_evalₐ J n)
  exact (Ideal.quotientEquivAlgOfEq (AdicCompletion J T) hk.symm).toRingEquiv.trans e |>.symm

private theorem completionQuotientEquiv_mk {T : Type u} [CommRing T]
    (J : Ideal T) (hJ : J.FG) (n : ℕ) (x : T) :
    completionQuotientEquiv J hJ n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap T (AdicCompletion J T) x) := by
  apply (completionQuotientEquiv J hJ n).symm.injective
  rw [RingEquiv.symm_apply_apply]
  change Ideal.Quotient.mk (J ^ n) x = AdicCompletion.evalₐ J n (AdicCompletion.of J T x)
  exact (AdicCompletion.evalₐ_of J n x).symm

/-- The stage comparison homomorphism is a ring equivalence. -/
def stageCompareEquiv (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    AdicAlgebraSystem.baseChangeStage (algebraMap A1 A2) I1 I2 hc
        (by exact map_pow_le_of_map_pow I1 I2 hI) ((toAdicSystem I1).obj B).obj n ≃+*
      ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj.right.stage n :=
  RingEquiv.ofBijective (stageCompareHom I1 I2 hc hI hI2 B n) (by
    let g := baseChangeHom (algebraMap A1 A2) I1 I2 hc (by exact map_pow_le_of_map_pow I1 I2 hI) n
    let e1 : AdicAlgebraSystem.baseChangeStage (algebraMap A1 A2) I1 I2 hc
        (by exact map_pow_le_of_map_pow I1 I2 hI) ((toAdicSystem I1).obj B).obj n ≃+*
        B.obj ⊗[A1] (A2 ⧸ I2 ^ (n : ℕ)) := by
      have hg : g.comp (Ideal.Quotient.mk (I1 ^ (stretchIndex hc n : ℕ))) =
          algebraMap A1 (A2 ⧸ I2 ^ (n : ℕ)) := rfl
      exact quotientTensorOverEquiv (B := B.obj) (I1 ^ (stretchIndex hc n : ℕ)) g hg
    let T := B.obj ⊗[A1] A2
    let J : Ideal T := tensorExtensionIdeal I2 B.obj
    let C := completedBaseChange A1 I2 B.obj
    have hsource : (I2 ^ (n : ℕ)).map
        (Algebra.TensorProduct.includeRight (R := A1) (A := B.obj)).toRingHom =
        J ^ (n : ℕ) := Ideal.map_pow _ _ _
    have htarget : (J ^ (n : ℕ)).map (algebraMap T C) =
        (I2 ^ (n : ℕ)).map (algebraMap A2 C) := by
      rw [← hsource, Ideal.map_map]
      rfl
    let e2 := (Algebra.TensorProduct.tensorQuotientEquiv (R := A1) A1 A2 B.obj
      (I2 ^ (n : ℕ))).toRingEquiv
    let e3 := completionQuotientEquiv J (hI2.map _) (n : ℕ)
    let e := e1.trans (e2.trans
      ((Ideal.quotientEquivAlgOfEq T hsource).toRingEquiv.trans
        (e3.trans (Ideal.quotientEquivAlgOfEq C htarget).toRingEquiv)))
    have he : e.toRingHom = stageCompareHom I1 I2 hc hI hI2 B n := by
      -- Local instance justification (noncanonical choice): extensionality uses the supplied stage scalar map.
      letI := (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n)).toAlgebra
      -- Local instance justification (noncanonical choice): extensionality uses the quotient base-change map g.
      letI := g.toAlgebra
      apply Algebra.TensorProduct.ringHom_ext
      · apply Ideal.Quotient.ringHom_ext
        ext b
        change e (tensorOverIncludeLeft _ _ (Ideal.Quotient.mk _ b)) = _
        have hl : e1 (tensorOverIncludeLeft _ _ (Ideal.Quotient.mk _ b)) =
            b ⊗ₜ[A1] (1 : A2 ⧸ I2 ^ (n : ℕ)) :=
          quotientTensorOverEquiv_left _ g _ b
        change (Ideal.quotientEquivAlgOfEq C htarget)
          (e3 ((Ideal.quotientEquivAlgOfEq T hsource) (e2 (e1 (tensorOverIncludeLeft _ _ (Ideal.Quotient.mk _ b)))))) = _
        rw [hl]
        change (Ideal.quotientEquivAlgOfEq C htarget)
          (e3 ((Ideal.quotientEquivAlgOfEq T hsource)
            (Ideal.Quotient.mk _ (b ⊗ₜ[A1] (1 : A2))))) = _
        rw [Ideal.quotientEquivAlgOfEq_mk, completionQuotientEquiv_mk, Ideal.quotientEquivAlgOfEq_mk]
        change Ideal.Quotient.mk _ (includeLeftToCompletion I2 B.obj b) =
          stageCompareLeftHom I1 I2 hc hI hI2 B n (Ideal.Quotient.mk _ b) *
            stageAlgebraMap I2 ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj n 1
        rw [map_one, mul_one]
        rfl
      · apply Ideal.Quotient.ringHom_ext
        ext a
        change e (tensorOverIncludeRight _ _ (Ideal.Quotient.mk _ a)) = _
        have hr : e1 (tensorOverIncludeRight _ _ (Ideal.Quotient.mk _ a)) =
            (1 : B.obj) ⊗ₜ[A1] (Ideal.Quotient.mk _ a) :=
          quotientTensorOverEquiv_right _ g _ (Ideal.Quotient.mk _ a)
        change (Ideal.quotientEquivAlgOfEq C htarget)
          (e3 ((Ideal.quotientEquivAlgOfEq T hsource) (e2 (e1 (tensorOverIncludeRight _ _ (Ideal.Quotient.mk _ a)))))) = _
        rw [hr]
        change (Ideal.quotientEquivAlgOfEq C htarget)
          (e3 ((Ideal.quotientEquivAlgOfEq T hsource)
            (Ideal.Quotient.mk _ ((1 : B.obj) ⊗ₜ[A1] a)))) = _
        rw [Ideal.quotientEquivAlgOfEq_mk, completionQuotientEquiv_mk, Ideal.quotientEquivAlgOfEq_mk]
        change Ideal.Quotient.mk _ (algebraMap A2 C a) =
          stageCompareLeftHom I1 I2 hc hI hI2 B n 1 *
            stageAlgebraMap I2 ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj n (Ideal.Quotient.mk _ a)
        rw [map_one, one_mul]
        rfl
    rw [← he]
    exact e.bijective)

/-- The underlying homomorphism of `stageCompareEquiv` is `stageCompareHom`. -/
theorem stageCompareEquiv_toRingHom (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    (stageCompareEquiv I1 I2 hc hI hI2 B n).toRingHom =
      stageCompareHom I1 I2 hc hI hI2 B n := by
  rfl

set_option maxHeartbeats 800000 in
private theorem stageCompareHom_transition (I1 : Ideal A1) (I2 : Ideal A2)
    {c : ℕ} (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) {m n : ℕ+} (hmn : m ≤ n) :
    (stageCompareHom I1 I2 hc hI hI2 B m).comp
        (AdicAlgebraSystem.baseChangeStageMap (algebraMap A1 A2) I1 I2 hc
          (by exact map_pow_le_of_map_pow I1 I2 hI) hmn ((toAdicSystem I1).obj B).obj).hom =
      (Ideal.Quotient.factor (Ideal.map_mono (f := algebraMap A2
          (completedBaseChange A1 I2 B.obj)) (Ideal.pow_le_pow_right hmn))).comp
        (stageCompareHom I1 I2 hc hI hI2 B n) := by
  let l := fun k ↦ tensorOverIncludeLeft
    (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc k))
    (baseChangeHom (algebraMap A1 A2) I1 I2 hc
      (by exact map_pow_le_of_map_pow I1 I2 hI) k)
  let r := fun k ↦ tensorOverIncludeRight
    (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc k))
    (baseChangeHom (algebraMap A1 A2) I1 I2 hc
      (by exact map_pow_le_of_map_pow I1 I2 hI) k)
  let t := (OrderDualInverseSystem.transitionMap ((toAdicSystem I1).obj B).obj.right
    (AdicAlgebraSystem.stretchIndex_mono hc hmn)).hom
  let q := Ideal.Quotient.factor (Ideal.map_mono (f := algebraMap A2
    (completedBaseChange A1 I2 B.obj)) (Ideal.pow_le_pow_right (I := I2) hmn))
  let a := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := I2) (show (m : ℕ) ≤ n from hmn))
  let s := (AdicAlgebraSystem.baseChangeStageMap (algebraMap A1 A2) I1 I2 hc
    (by exact map_pow_le_of_map_pow I1 I2 hI) hmn ((toAdicSystem I1).obj B).obj).hom
  have hfg : ((l m).comp t).comp
      (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n)) =
      ((r m).comp a).comp (baseChangeHom (algebraMap A1 A2) I1 I2 hc
        (by exact map_pow_le_of_map_pow I1 I2 hI) n) := by
    -- The balancing relation uses the explicit quotient scalar maps at stage m.
    letI := (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc m)).toAlgebra
    letI := (baseChangeHom (algebraMap A1 A2) I1 I2 hc
      (by exact map_pow_le_of_map_pow I1 I2 hI) m).toAlgebra
    apply Ideal.Quotient.ringHom_ext
    ext x
    exact RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
        (R := A1 ⧸ I1 ^ (stretchIndex hc m : ℕ))
        (A := ((toAdicSystem I1).obj B).obj.right.stage (stretchIndex hc m))
        (B := A2 ⧸ I2 ^ (m : ℕ))) (Ideal.Quotient.mk _ x)
  have sl : s.comp (l n) = (l m).comp t :=
    tensorOverLift_comp_includeLeft _ _ _ _ hfg
  have sr : s.comp (r n) = (r m).comp a :=
    tensorOverLift_comp_includeRight _ _ _ _ hfg
  apply tensorOver_hom_ext
    (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n))
    (baseChangeHom (algebraMap A1 A2) I1 I2 hc
      (by exact map_pow_le_of_map_pow I1 I2 hI) n)
  · calc
      _ = (stageCompareHom I1 I2 hc hI hI2 B m).comp (s.comp (l n)) := rfl
      _ = (stageCompareHom I1 I2 hc hI hI2 B m).comp ((l m).comp t) :=
        congrArg (fun k ↦ (stageCompareHom I1 I2 hc hI hI2 B m).comp k) sl
      _ = ((stageCompareHom I1 I2 hc hI hI2 B m).comp (l m)).comp t := rfl
      _ = (stageCompareLeftHom I1 I2 hc hI hI2 B m).comp t :=
        congrArg (fun k ↦ k.comp t) (stageCompareHom_includeLeft I1 I2 hc hI hI2 B m)
      _ = q.comp (stageCompareLeftHom I1 I2 hc hI hI2 B n) := by
        apply Ideal.Quotient.ringHom_ext
        ext b
        rfl
      _ = _ := congrArg (fun k ↦ q.comp k)
        (stageCompareHom_includeLeft I1 I2 hc hI hI2 B n).symm
  · calc
      _ = (stageCompareHom I1 I2 hc hI hI2 B m).comp (s.comp (r n)) := rfl
      _ = (stageCompareHom I1 I2 hc hI hI2 B m).comp ((r m).comp a) :=
        congrArg (fun k ↦ (stageCompareHom I1 I2 hc hI hI2 B m).comp k) sr
      _ = ((stageCompareHom I1 I2 hc hI hI2 B m).comp (r m)).comp a := rfl
      _ = (stageAlgebraMap I2
          ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj m).comp a :=
        congrArg (fun k ↦ k.comp a) (stageCompareHom_includeRight I1 I2 hc hI hI2 B m)
      _ = q.comp (stageAlgebraMap I2
          ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj n) := by
        apply Ideal.Quotient.ringHom_ext
        ext x
        rfl
      _ = _ := congrArg (fun k ↦ q.comp k)
        (stageCompareHom_includeRight I1 I2 hc hI hI2 B n).symm

/-- The stage comparison equivalences commute with transition maps of the quotient systems. -/
private theorem baseChangeRightIso_naturality (I1 : Ideal A1) (I2 : Ideal A2)
    {c : ℕ} (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) :
    let F := ((toAdicSystem I1 ⋙
      AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
        (by exact map_pow_le_of_map_pow I1 I2 hI)).obj B).obj.right
    let G := ((baseChange I1 I2 hc hI hI2 ⋙ toAdicSystem I2).obj B).obj.right
    let app := fun i : ℕ+ᵒᵈ ↦
      (stageCompareEquiv I1 I2 hc hI hI2 B (OrderDual.ofDual i)).toCommRingCatIso
    ∀ {i j : ℕ+ᵒᵈ} (f : i ⟶ j),
      F.map f ≫ (app j).hom = (app i).hom ≫ G.map f := by
  intro F G app i j f
  apply CommRingCat.hom_ext
  exact stageCompareHom_transition I1 I2 hc hI hI2 B (leOfHom f)

-- Local declaration justification (metaprogramming implementation): expose the
-- private quotient-system construction to the public object comparison.
set_option backward.privateInPublic true in
/-- The stage comparison equivalences identify the underlying quotient systems. -/
private def baseChangeRightIso (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) :
    ((toAdicSystem I1 ⋙
      AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
        (by exact map_pow_le_of_map_pow I1 I2 hI)).obj B).obj.right ≅
      ((baseChange I1 I2 hc hI hI2 ⋙ toAdicSystem I2).obj B).obj.right :=
  NatIso.ofComponents
    (fun i ↦ (stageCompareEquiv I1 I2 hc hI hI2 B (OrderDual.ofDual i)).toCommRingCatIso)
    (by exact baseChangeRightIso_naturality I1 I2 hc hI hI2 B)

/-- The quotient-system comparison respects the coefficient-system structure maps. -/
private theorem baseChangeRightIso_under (I1 : Ideal A1) (I2 : Ideal A2)
    {c : ℕ} (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) :
    ((toAdicSystem I1 ⋙
      AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
        (by exact map_pow_le_of_map_pow I1 I2 hI)).obj B).obj.hom ≫
      (baseChangeRightIso I1 I2 hc hI hI2 B).hom =
        ((baseChange I1 I2 hc hI hI2 ⋙ toAdicSystem I2).obj B).obj.hom := by
  apply NatTrans.ext
  funext i
  apply CommRingCat.hom_ext
  exact stageCompareHom_includeRight I1 I2 hc hI hI2 B (OrderDual.ofDual i)

-- Local declaration justification (metaprogramming implementation): the exposed
-- object comparison uses its private, concretely constructed quotient-system isomorphism.
set_option backward.privateInPublic true in
/-- Objectwise isomorphism of adic systems comparing systems base change of
`toAdicSystem I1` with `toAdicSystem I2` of completed base change. -/
def baseChangeObjIso (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) :
    (toAdicSystem I1 ⋙
        AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
          (by exact map_pow_le_of_map_pow I1 I2 hI)).obj B ≅
      (baseChange I1 I2 hc hI hI2 ⋙ toAdicSystem I2).obj B :=
  ObjectProperty.isoMk _
    (Under.isoMk (baseChangeRightIso I1 I2 hc hI hI2 B)
      (by exact baseChangeRightIso_under I1 I2 hc hI hI2 B))

/-- The right-leg component of `baseChangeObjIso` at stage `n` is
`stageCompareEquiv`. -/
theorem baseChangeObjIso_stage (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    (Under.Hom.right (baseChangeObjIso I1 I2 hc hI hI2 B).hom.hom).app
        (OrderDual.toDual n) =
      (stageCompareEquiv I1 I2 hc hI hI2 B n).toCommRingCatIso.hom := by
  rfl

private theorem completedBaseChangeMap_includeLeft (I2 : Ideal A2)
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A1 B] [Algebra A1 B']
    (f : B →ₐ[A1] B') (b : B) :
    completedBaseChangeMap I2 f (includeLeftToCompletion I2 B b) =
      includeLeftToCompletion I2 B' (f b) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ _ n
      (AdicCompletion.liftRingHom _ (completedBaseChangeQuotientMap I2 f)
        (completedBaseChangeQuotientMap_compatible I2 f)
        (includeLeftToCompletion I2 B b)) = _
  rw [AdicCompletion.evalₐ_liftRingHom]
  change (Ideal.quotientMap (tensorExtensionIdeal I2 B' ^ n)
      (Algebra.TensorProduct.map f (AlgHom.id A1 A2)).toRingHom
      (tensorExtensionIdeal_map_le_comap I2 f n))
      (AdicCompletion.evalₐ _ n (AdicCompletion.of _ _ (b ⊗ₜ[A1] (1 : A2)))) =
    AdicCompletion.evalₐ _ n (AdicCompletion.of _ _ (f b ⊗ₜ[A1] (1 : A2)))
  rw [AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  rfl

private theorem stageCompareHom_naturality (I1 : Ideal A1) (I2 : Ideal A2)
    {c : ℕ} (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    {B B' : TopologicallyFiniteType.{u} A1 I1} (f : B ⟶ B') (n : ℕ+) :
    (stageCompareHom I1 I2 hc hI hI2 B' n).comp
        ((Under.Hom.right ((toAdicSystem I1 ⋙
          AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
            (by exact map_pow_le_of_map_pow I1 I2 hI)).map f).hom).app
          (OrderDual.toDual n)).hom =
      (CommAlgCat.adicQuotientMap I2 (completedBaseChangeMap I2 f.hom.hom) n).comp
        (stageCompareHom I1 I2 hc hI hI2 B n) := by
  let l := fun X : TopologicallyFiniteType.{u} A1 I1 ↦ tensorOverIncludeLeft
    (stageAlgebraMap I1 ((toAdicSystem I1).obj X).obj (stretchIndex hc n))
    (baseChangeHom (algebraMap A1 A2) I1 I2 hc
      (by exact map_pow_le_of_map_pow I1 I2 hI) n)
  let r := fun X : TopologicallyFiniteType.{u} A1 I1 ↦ tensorOverIncludeRight
    (stageAlgebraMap I1 ((toAdicSystem I1).obj X).obj (stretchIndex hc n))
    (baseChangeHom (algebraMap A1 A2) I1 I2 hc
      (by exact map_pow_le_of_map_pow I1 I2 hI) n)
  let t := CommAlgCat.adicQuotientMap I1 f.hom.hom (stretchIndex hc n)
  let q := CommAlgCat.adicQuotientMap I2 (completedBaseChangeMap I2 f.hom.hom) n
  let s := ((Under.Hom.right ((toAdicSystem I1 ⋙
    AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
      (by exact map_pow_le_of_map_pow I1 I2 hI)).map f).hom).app
    (OrderDual.toDual n)).hom
  have hf : t.comp
      (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n)) =
      stageAlgebraMap I1 ((toAdicSystem I1).obj B').obj (stretchIndex hc n) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    exact congrArg (Ideal.Quotient.mk _) (f.hom.hom.commutes x)
  have sl : s.comp (l B) = (l B').comp t :=
    tensorOverMap_comp_includeLeft _ _ _ _ t (RingHom.id _) hf (RingHom.id_comp _)
  have sr : s.comp (r B) = (r B').comp (RingHom.id _) :=
    tensorOverMap_comp_includeRight _ _ _ _ t (RingHom.id _) hf (RingHom.id_comp _)
  have hqleft : (stageCompareLeftHom I1 I2 hc hI hI2 B' n).comp t =
      q.comp (stageCompareLeftHom I1 I2 hc hI hI2 B n) := by
    apply Ideal.Quotient.ringHom_ext
    ext b
    exact congrArg (Ideal.Quotient.mk _)
      (completedBaseChangeMap_includeLeft I2 f.hom.hom b).symm
  have hqright : (stageAlgebraMap I2
      ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B')).obj n).comp
        (RingHom.id _) =
      q.comp (stageAlgebraMap I2
        ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj n) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    exact congrArg (Ideal.Quotient.mk _)
      ((completedBaseChangeMap I2 f.hom.hom).commutes x).symm
  apply tensorOver_hom_ext
    (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n))
    (baseChangeHom (algebraMap A1 A2) I1 I2 hc
      (by exact map_pow_le_of_map_pow I1 I2 hI) n)
  · exact (congrArg (fun k ↦ (stageCompareHom I1 I2 hc hI hI2 B' n).comp k) sl).trans
      ((congrArg (fun k ↦ k.comp t)
        (stageCompareHom_includeLeft I1 I2 hc hI hI2 B' n)).trans
        (hqleft.trans (congrArg (fun k ↦ q.comp k)
          (stageCompareHom_includeLeft I1 I2 hc hI hI2 B n).symm)))
  · exact (congrArg (fun k ↦ (stageCompareHom I1 I2 hc hI hI2 B' n).comp k) sr).trans
      ((congrArg (fun k ↦ k.comp (RingHom.id _))
        (stageCompareHom_includeRight I1 I2 hc hI hI2 B' n)).trans
        (hqright.trans (congrArg (fun k ↦ q.comp k)
          (stageCompareHom_includeRight I1 I2 hc hI hI2 B n).symm)))

/-- The objectwise comparison of adic systems is natural in complete algebras. -/
private theorem baseChangeObjIso_naturality (I1 : Ideal A1) (I2 : Ideal A2)
    {c : ℕ} (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG) :
    ∀ {B B' : TopologicallyFiniteType.{u} A1 I1} (f : B ⟶ B'),
      (toAdicSystem I1 ⋙
        AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
          (by exact map_pow_le_of_map_pow I1 I2 hI)).map f ≫
        (baseChangeObjIso I1 I2 hc hI hI2 B').hom =
      (baseChangeObjIso I1 I2 hc hI hI2 B).hom ≫
        (baseChange I1 I2 hc hI hI2 ⋙ toAdicSystem I2).map f := by
  intro B B' f
  apply ObjectProperty.hom_ext
  apply Under.UnderMorphism.ext
  apply NatTrans.ext
  funext i
  apply CommRingCat.hom_ext
  exact stageCompareHom_naturality I1 I2 hc hI hI2 f (OrderDual.ofDual i)

/-- Natural isomorphism identifying systems base change of `toAdicSystem I1`
with `toAdicSystem I2` of completed base change. -/
def baseChangeToAdicSystemIso (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG) :
    toAdicSystem I1 ⋙
        AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
          (by exact map_pow_le_of_map_pow I1 I2 hI) ≅
      baseChange I1 I2 hc hI hI2 ⋙ toAdicSystem I2 :=
  NatIso.ofComponents (baseChangeObjIso I1 I2 hc hI hI2)
    (by exact baseChangeObjIso_naturality I1 I2 hc hI hI2)

/-- Components of `baseChangeToAdicSystemIso` are `baseChangeObjIso`. -/
theorem baseChangeToAdicSystemIso_app (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) :
    (baseChangeToAdicSystemIso I1 I2 hc hI hI2).app B =
      baseChangeObjIso I1 I2 hc hI hI2 B := by
  rfl

/-- Stage components of `baseChangeToAdicSystemIso` are `stageCompareEquiv`. -/
theorem baseChangeToAdicSystemIso_stage (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    (Under.Hom.right ((baseChangeToAdicSystemIso I1 I2 hc hI hI2).app B).hom.hom).app
        (OrderDual.toDual n) =
      (stageCompareEquiv I1 I2 hc hI hI2 B n).toCommRingCatIso.hom := by
  rfl

/-- When both ideals are finitely generated, inverse limits transport the
comparison isomorphism to an identification of completed base change with
systems base change. -/
def baseChangeLimitIso (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI1 : I1.FG) (hI2 : I2.FG) :
    AdicAlgebraSystem.limitFunctor I1 hI1 ⋙ baseChange I1 I2 hc hI hI2 ≅
      AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
          (by exact map_pow_le_of_map_pow I1 I2 hI) ⋙
        AdicAlgebraSystem.limitFunctor I2 hI2 :=
  let S :=
    AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
      (by exact map_pow_le_of_map_pow I1 I2 hI)
  let Cplt := baseChange I1 I2 hc hI hI2
  let L1 := AdicAlgebraSystem.limitFunctor I1 hI1
  let L2 := AdicAlgebraSystem.limitFunctor I2 hI2
  let T1 := toAdicSystem I1
  let T2 := toAdicSystem I2
  let α := baseChangeToAdicSystemIso I1 I2 hc hI hI2
  (Functor.rightUnitor (L1 ⋙ Cplt)).symm ≪≫
    Functor.isoWhiskerLeft (L1 ⋙ Cplt) (AdicAlgebraSystem.limitFunctorUnitIso I2 hI2) ≪≫
    (Functor.associator (L1 ⋙ Cplt) T2 L2).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator L1 Cplt T2) L2 ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft L1 α.symm) L2 ≪≫
    Functor.isoWhiskerRight (Functor.associator L1 T1 S).symm L2 ≪≫
    Functor.associator (L1 ⋙ T1) S L2 ≪≫
    Functor.isoWhiskerRight (AdicAlgebraSystem.limitFunctorCounitIso I1 hI1) (S ⋙ L2) ≪≫
    Functor.leftUnitor (S ⋙ L2)

end CommAlgCat.TopologicallyFiniteType
