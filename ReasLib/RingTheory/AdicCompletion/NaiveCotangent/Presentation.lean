/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType.Tower
public import ReasLib.RingTheory.AdicCompletion.Polynomial.Evaluation

/-!
# Composite completed polynomial presentations

Given presentations `B = A[x_ι]^∧ / J` and `C = B[y_κ]^∧ / J'`, the composite
presentation is `C = A[x_ι, y_κ]^∧ / K`, together with the polynomial-ring
maps that form the columns of the Jacobi–Zariski snake diagram.
-/

@[expose] public section

noncomputable section

universe u

open Algebra.NaiveCotangent.Adic

namespace Algebra.NaiveCotangent.Adic

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- Completeness of `A[x_ι]^∧` along the extended ideal `I · A[x_ι]^∧`, so that
completed evaluation into a polynomial completion is defined. Finite generation
of `I` is used via `AdicCompletion.isAdicComplete`. -/
@[implicit_reducible] def polynomialCompletion_isAdicComplete_map (ι : Type u) :
    IsAdicComplete (I.map (algebraMap A (polynomialCompletion A I ι)))
      (polynomialCompletion A I ι) :=
  (IsAdicComplete.map_algebraMap_iff (R := A) (S := polynomialCompletion A I ι)
      (M := polynomialCompletion A I ι) I).mpr
    ((IsAdicComplete.map_algebraMap_iff (R := A) (S := MvPolynomial ι A)
        (M := polynomialCompletion A I ι) I).mp
      (AdicCompletion.isAdicComplete
        (Ideal.FG.map (IsNoetherian.noetherian I)
          (algebraMap A (MvPolynomial ι A)))))

/-- Every completed polynomial has a polynomial representative modulo the coefficient ideal. -/
private theorem exists_polynomial_mod {A ι : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (x : polynomialCompletion A I ι) :
    ∃ p : MvPolynomial ι A,
      x - AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p ∈
        (I • ⊤ : Submodule A (polynomialCompletion A I ι)) := by
  obtain ⟨p, hp⟩ := Submodule.mkQ_surjective
    ((polynomialIdeal A I ι) ^ 1 • ⊤ : Submodule (MvPolynomial ι A) (MvPolynomial ι A))
    (AdicCompletion.eval (polynomialIdeal A I ι) (MvPolynomial ι A) 1 x)
  refine ⟨p, ?_⟩
  have hx : x - AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p ∈
      ((polynomialIdeal A I ι) • ⊤ : Submodule (MvPolynomial ι A) (polynomialCompletion A I ι)) := by
    have hpow : ((polynomialIdeal A I ι) • ⊤ :
        Submodule (MvPolynomial ι A) (polynomialCompletion A I ι)) =
        (AdicCompletion.eval (polynomialIdeal A I ι) (MvPolynomial ι A) 1).ker := by
      have hker := AdicCompletion.pow_smul_top_eq_ker_eval
        (I := polynomialIdeal A I ι) (M := MvPolynomial ι A) (n := 1)
        (Ideal.FG.map hI (algebraMap A (MvPolynomial ι A)))
      simpa only [pow_one] using hker
    rw [hpow,
      LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, sub_eq_zero]
    exact hp.symm
  change x - AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p ∈
    (((polynomialIdeal A I ι) • ⊤ :
      Submodule (MvPolynomial ι A) (polynomialCompletion A I ι)).restrictScalars A) at hx
  change x - AdicCompletion.of (polynomialIdeal A I ι) (MvPolynomial ι A) p ∈
    (((I.map (algebraMap A (MvPolynomial ι A))) • ⊤ :
      Submodule (MvPolynomial ι A) (polynomialCompletion A I ι)).restrictScalars A) at hx
  rwa [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top] at hx

variable {B : Type u} [CommRing B] [Algebra A B]

/-- Completeness of `B[y_κ]^∧` along the extended ideal of `I`, as an
`A`-algebra. Finite generation of `I B` follows from finite generation of `I`. -/
@[implicit_reducible] def polynomialCompletion_tower_isAdicComplete_map (ι : Type u) :
    IsAdicComplete
      (I.map (algebraMap A (polynomialCompletion B (I.map (algebraMap A B)) ι)))
      (polynomialCompletion B (I.map (algebraMap A B)) ι) :=
  (IsAdicComplete.map_algebraMap_iff (R := A)
      (S := polynomialCompletion B (I.map (algebraMap A B)) ι)
      (M := polynomialCompletion B (I.map (algebraMap A B)) ι) I).mpr
    ((IsAdicComplete.map_algebraMap_iff (R := A) (S := B)
        (M := polynomialCompletion B (I.map (algebraMap A B)) ι) I).mp
      ((IsAdicComplete.map_algebraMap_iff (R := B) (S := MvPolynomial ι B)
          (M := polynomialCompletion B (I.map (algebraMap A B)) ι)
          (I.map (algebraMap A B))).mp
        (AdicCompletion.isAdicComplete
          (Ideal.FG.map
            (Ideal.FG.map (IsNoetherian.noetherian I) (algebraMap A B))
            (algebraMap B (MvPolynomial ι B))))))

variable {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable [Algebra.TopologicallyFiniteType I C]
variable {ι κ : Type u}

namespace Presentation

/-- Completed evaluation at the variables of two successive presentations. -/
def compToAlgHom (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) : polynomialCompletion A I (κ ⊕ ι) →ₐ[A] C :=
  adicAeval I (Sum.elim (fun j ↦ Q.toAlgHom (X (I.map (algebraMap A B)) j))
    (fun i ↦ algebraMap B C (P.toAlgHom (X I i))))

/-- Completed evaluation at two successive sets of presentation variables is surjective. -/
theorem compToAlgHom_surjective (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) : Function.Surjective (compToAlgHom Q P) := by
  let D := polynomialCompletion A I (κ ⊕ ι)
  let f := Presentation.compToAlgHom Q P
  let π := Ideal.Quotient.mkₐ A (I.map (algebraMap A C))
  let inc : polynomialCompletion A I ι →ₐ[A] D :=
    @adicAeval _ _ _ _ _ _ I (polynomialCompletion_isAdicComplete_map (κ ⊕ ι))
      (fun i ↦ X I (Sum.inr i))
  have hinc : f.comp inc = (IsScalarTower.toAlgHom A B C).comp P.toAlgHom := by
    rw [eq_adicAeval (IsNoetherian.noetherian I) (f.comp inc),
      eq_adicAeval (IsNoetherian.noetherian I) ((IsScalarTower.toAlgHom A B C).comp P.toAlgHom)]
    congr 1
    funext i
    simp [f, inc, Presentation.compToAlgHom, adicAeval_X]
  have hB (b : B) : π (algebraMap B C b) ∈ (π.comp f).range := by
    obtain ⟨x, rfl⟩ := P.surjective b
    exact ⟨inc x, congrArg π (AlgHom.congr_fun hinc x)⟩
  have hX (j : κ) : π (Q.toAlgHom (X (I.map (algebraMap A B)) j)) ∈ (π.comp f).range := by
    refine ⟨X I (Sum.inl j), ?_⟩
    simp [f, Presentation.compToAlgHom, adicAeval_X]
  have hpoly (p : MvPolynomial κ B) :
      π (Q.toAlgHom (algebraMap (MvPolynomial κ B) _ p)) ∈ (π.comp f).range := by
    induction p using MvPolynomial.induction_on with
    | C b =>
        rw [show MvPolynomial.C b = algebraMap B (MvPolynomial κ B) b from rfl,
          ← IsScalarTower.algebraMap_apply]
        simpa using hB b
    | add p q hp hq => simpa using (π.comp f).range.add_mem hp hq
    | mul_X p j hp =>
        rw [map_mul, map_mul, map_mul]
        exact (π.comp f).range.mul_mem hp (hX j)
  have hmod : Function.Surjective (π.comp f) := by
    intro c
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨q, rfl⟩ := Q.surjective c
    obtain ⟨p, hp⟩ := exists_polynomial_mod (I.map (algebraMap A B))
      (Ideal.FG.map (IsNoetherian.noetherian I) (algebraMap A B)) q
    have hq : Q.toAlgHom (q - algebraMap (MvPolynomial κ B) _ p) ∈
        ((I.map (algebraMap A B)) • ⊤ : Submodule B C) := by
      apply (Submodule.map_le_iff_le_comap.mp (show
        Submodule.map Q.toAlgHom.toLinearMap ((I.map (algebraMap A B)) • ⊤) ≤
          (I.map (algebraMap A B)) • ⊤ from ?_)) hp
      rw [Submodule.map_smul'']
      exact smul_mono_right _ le_top
    have hzero : π (Q.toAlgHom q) =
        π (Q.toAlgHom (algebraMap (MvPolynomial κ B) _ p)) := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa [Ideal.smul_top_eq_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq A B C] using hq
    change π (Q.toAlgHom q) ∈ (π.comp f).range
    rw [hzero]
    exact hpoly p
  letI : IsAdicComplete I D :=
    (IsAdicComplete.map_algebraMap_iff (R := A) (S := MvPolynomial (κ ⊕ ι) A)
      (M := D) I).mp
      (AdicCompletion.isAdicComplete
        (Ideal.FG.map (IsNoetherian.noetherian I) (algebraMap A (MvPolynomial (κ ⊕ ι) A))))
  apply surjective_of_mkQ_comp_surjective (I := I) (f := f.toLinearMap)
  intro c
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A C)) c
  obtain ⟨d, hd⟩ := hmod (π c)
  refine ⟨d, ?_⟩
  change Submodule.Quotient.mk (f d) = Submodule.Quotient.mk c
  rw [Submodule.Quotient.eq]
  have hdc : f d - c ∈ I.map (algebraMap A C) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π (f d - c) = 0
    rw [map_sub, ← hd]
    simp
  simpa [Ideal.smul_top_eq_map] using hdc

/-- The composite completed polynomial presentation obtained from two successive presentations. -/
def comp (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) : Presentation A C I (κ ⊕ ι) where
  toAlgHom := compToAlgHom Q P
  surjective := compToAlgHom_surjective Q P

/-- The structure map of the composite presentation evaluates the `y`-variables
at the images of the `Q`-variables in `C`. -/
theorem comp_X_inl (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (j : κ) :
    (comp Q P).toAlgHom (X I (Sum.inl j)) =
      Q.toAlgHom (X (I.map (algebraMap A B)) j) := by
  exact adicAeval_X I _ (Sum.inl j)

/-- The structure map of the composite presentation evaluates the `x`-variables
at the images of the `P`-variables in `C`. -/
theorem comp_X_inr (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (i : ι) :
    (comp Q P).toAlgHom (X I (Sum.inr i)) = algebraMap B C (P.toAlgHom (X I i)) := by
  exact adicAeval_X I _ (Sum.inr i)

/-- The composite presentation is a surjective `A`-algebra map
`A[x_ι, y_κ]^∧ →ₐ[A] C`. -/
theorem comp_surjective (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) :
    Function.Surjective (comp Q P).toAlgHom :=
  (comp Q P).surjective

/-- The map of completed polynomial rings `A[x_ι]^∧ →ₐ[A] A[x_ι, y_κ]^∧` sending
`x_i` to the corresponding composite indeterminate. -/
def toComp (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) :
    polynomialCompletion A I ι →ₐ[A] polynomialCompletion A I (κ ⊕ ι) :=
  @adicAeval _ _ _ _ _ _ I (polynomialCompletion_isAdicComplete_map (I := I) (κ ⊕ ι))
    fun i ↦ X I (Sum.inr i)

/-- `toComp` sends the indeterminate `X I i` to `X I (Sum.inr i)`. -/
theorem toComp_X (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (i : ι) :
    (toComp Q P) (X I i) = X I (Sum.inr i) := by
  exact @adicAeval_X _ _ _ _ _ _ I
    (polynomialCompletion_isAdicComplete_map (I := I) (κ ⊕ ι)) _ i

/-- The completed variable inclusion commutes with the presentation maps. -/
theorem toCompHom_over (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (x : polynomialCompletion A I ι) :
    (comp Q P).toAlgHom (toComp Q P x) = algebraMap B C (P.toAlgHom x) := by
  have h : (comp Q P).toAlgHom.comp (toComp Q P) =
      (IsScalarTower.toAlgHom A B C).comp P.toAlgHom := by
    rw [eq_adicAeval (IsNoetherian.noetherian I) ((comp Q P).toAlgHom.comp (toComp Q P)),
      eq_adicAeval (IsNoetherian.noetherian I)
        ((IsScalarTower.toAlgHom A B C).comp P.toAlgHom)]
    congr 1
    funext i
    simp [comp, compToAlgHom, toComp, adicAeval_X]
  exact AlgHom.congr_fun h x

/-- The morphism of `A`-extensions induced by `toComp`. -/
def toCompHom (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) :
    P.toExtension.Hom (comp Q P).toExtension where
  toRingHom := (toComp Q P).toRingHom
  toRingHom_algebraMap x := by
    change (toComp Q P) (algebraMap A (polynomialCompletion A I ι) x) =
      algebraMap A (polynomialCompletion A I (κ ⊕ ι)) (algebraMap A A x)
    exact (toComp Q P).commutes x
  algebraMap_toRingHom := toCompHom_over Q P

/-- The map of completed polynomial rings `A[x_ι, y_κ]^∧ →ₐ[A] B[y_κ]^∧` sending
`y_j` to the `B`-indeterminate and `x_i` to the image of the `P`-variable. -/
def ofComp (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) :
    polynomialCompletion A I (κ ⊕ ι) →ₐ[A]
      polynomialCompletion B (I.map (algebraMap A B)) κ :=
  @adicAeval _ _ _ _ _ _ I
    (polynomialCompletion_tower_isAdicComplete_map (I := I) (B := B) κ)
    (Sum.elim (X (I.map (algebraMap A B)))
    (fun i ↦ algebraMap B (polynomialCompletion B (I.map (algebraMap A B)) κ)
      (P.toAlgHom (X I i))))

/-- `ofComp` sends a `y`-indeterminate to the corresponding `B[y_κ]^∧`
indeterminate. -/
theorem ofComp_X_inl (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (j : κ) :
    (ofComp Q P) (X I (Sum.inl j)) = X (I.map (algebraMap A B)) j := by
  exact @adicAeval_X _ _ _ _ _ _ I
    (polynomialCompletion_tower_isAdicComplete_map (I := I) (B := B) κ) _ (Sum.inl j)

/-- `ofComp` sends an `x`-indeterminate to the constant given by the image of
the corresponding `P`-variable. -/
theorem ofComp_X_inr (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (i : ι) :
    (ofComp Q P) (X I (Sum.inr i)) =
      algebraMap B (polynomialCompletion B (I.map (algebraMap A B)) κ)
        (P.toAlgHom (X I i)) := by
  exact @adicAeval_X _ _ _ _ _ _ I
    (polynomialCompletion_tower_isAdicComplete_map (I := I) (B := B) κ) _ (Sum.inr i)

/-- Changing the old completed-polynomial coefficients through a surjective
presentation remains surjective after adjoining the relative variables. -/
theorem ofComp_surjective (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) : Function.Surjective (ofComp Q P) := by
  let D := polynomialCompletion A I (κ ⊕ ι)
  let T := polynomialCompletion B (I.map (algebraMap A B)) κ
  letI := polynomialCompletion_tower_isAdicComplete_map (I := I) (B := B) κ
  let f := ofComp Q P
  let π := Ideal.Quotient.mkₐ A (I.map (algebraMap A T))
  let inc : polynomialCompletion A I ι →ₐ[A] D :=
    @adicAeval _ _ _ _ _ _ I (polynomialCompletion_isAdicComplete_map (κ ⊕ ι))
      (fun i ↦ X I (Sum.inr i))
  have hinc : f.comp inc = (IsScalarTower.toAlgHom A B T).comp P.toAlgHom := by
    rw [eq_adicAeval (IsNoetherian.noetherian I) (f.comp inc),
      eq_adicAeval (IsNoetherian.noetherian I) ((IsScalarTower.toAlgHom A B T).comp P.toAlgHom)]
    congr 1
    funext i
    simp [f, inc, ofComp, adicAeval_X, T]
  have hB (b : B) : π (algebraMap B T b) ∈ (π.comp f).range := by
    obtain ⟨x, rfl⟩ := P.surjective b
    exact ⟨inc x, congrArg π (AlgHom.congr_fun hinc x)⟩
  have hX (j : κ) : π (X (I.map (algebraMap A B)) j) ∈ (π.comp f).range := by
    exact ⟨X I (Sum.inl j), congrArg π (ofComp_X_inl Q P j)⟩
  have hpoly (p : MvPolynomial κ B) :
      π (algebraMap (MvPolynomial κ B) T p) ∈ (π.comp f).range := by
    induction p using MvPolynomial.induction_on with
    | C b =>
        rw [show MvPolynomial.C b = algebraMap B (MvPolynomial κ B) b from rfl,
          ← IsScalarTower.algebraMap_apply]
        exact hB b
    | add p q hp hq => simpa using (π.comp f).range.add_mem hp hq
    | mul_X p j hp =>
        rw [map_mul, map_mul]
        exact (π.comp f).range.mul_mem hp (hX j)
  have hmod : Function.Surjective (π.comp f) := by
    intro t
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨p, hp⟩ := exists_polynomial_mod (I.map (algebraMap A B))
      (Ideal.FG.map (IsNoetherian.noetherian I) (algebraMap A B)) t
    change t - algebraMap (MvPolynomial κ B) T p ∈
      ((I.map (algebraMap A B)) • ⊤ : Submodule B T) at hp
    have hzero : π t = π (algebraMap (MvPolynomial κ B) T p) := by
      rw [← sub_eq_zero, ← map_sub]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa [T, Ideal.smul_top_eq_map, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq A B
          (polynomialCompletion B (I.map (algebraMap A B)) κ)] using hp
    change π t ∈ (π.comp f).range
    rw [hzero]
    exact hpoly p
  letI : IsAdicComplete I T :=
    (IsAdicComplete.map_algebraMap_iff (R := A) (S := T) (M := T) I).mp inferInstance
  letI : IsAdicComplete I D :=
    (IsAdicComplete.map_algebraMap_iff (R := A) (S := MvPolynomial (κ ⊕ ι) A)
      (M := D) I).mp
      (AdicCompletion.isAdicComplete
        (Ideal.FG.map (IsNoetherian.noetherian I) (algebraMap A (MvPolynomial (κ ⊕ ι) A))))
  change Function.Surjective f
  apply surjective_of_mkQ_comp_surjective (I := I) (f := f.toLinearMap)
  intro t
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A T)) t
  obtain ⟨d, hd⟩ := hmod (π t)
  refine ⟨d, ?_⟩
  change Submodule.Quotient.mk (f d) = Submodule.Quotient.mk t
  rw [Submodule.Quotient.eq]
  have hdt : f d - t ∈ I.map (algebraMap A T) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π (f d - t) = 0
    rw [map_sub, ← hd]
    simp
  simpa [Ideal.smul_top_eq_map] using hdt

/-- Completed evaluation into the intermediate-base presentation commutes with its quotient map. -/
theorem ofCompHom_over (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) (x : polynomialCompletion A I (κ ⊕ ι)) :
    Q.toAlgHom (ofComp Q P x) = (comp Q P).toAlgHom x := by
  have h : (Q.toAlgHom.restrictScalars A).comp (ofComp Q P) = (comp Q P).toAlgHom := by
    rw [eq_adicAeval (IsNoetherian.noetherian I)
      ((Q.toAlgHom.restrictScalars A).comp (ofComp Q P))]
    change adicAeval I _ = adicAeval I _
    congr 1
    funext i
    cases i <;> simp [ofComp, adicAeval_X]
  exact AlgHom.congr_fun h x

/-- The morphism of extensions induced by `ofComp`. -/
def ofCompHom (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (P : Presentation A B I ι) :
    (comp Q P).toExtension.Hom Q.toExtension where
  toRingHom := (ofComp Q P).toRingHom
  toRingHom_algebraMap x := by
    change (ofComp Q P) (algebraMap A (polynomialCompletion A I (κ ⊕ ι)) x) =
      algebraMap B (polynomialCompletion B (I.map (algebraMap A B)) κ) (algebraMap A B x)
    rw [← IsScalarTower.algebraMap_apply]
    exact (ofComp Q P).commutes x
  algebraMap_toRingHom x := ofCompHom_over Q P x

end Presentation

end Algebra.NaiveCotangent.Adic
