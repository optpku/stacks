/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import ReasLib.NumberTheory.Automorphic.CuspForm
public import ReasLib.NumberTheory.Automorphic.Eigenform
public import ReasLib.NumberTheory.Automorphic.Hecke

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.Scheme Matrix
open Finset
noncomputable section
universe u v
namespace AlgebraicGeometry.SchemeOverField
variable {k : Type u} [Field k]
variable {Λ : Type v} [CommRing Λ]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
variable [Fintype k] [Invertible (ringChar k : Λ)]

/-- A completed residue representative obtained from the canonical integral residue section. -/
def residueRep (v : closedPoints X.left) (a : X.left.residueField v.1) : completion X v :=
  (residueSectionIntegers X v a).val

/-- Canonical residue representatives lie in the local integers. -/
theorem residueRep_mem_integers (v : closedPoints X.left) (a : X.left.residueField v.1) :
    residueRep X v a ∈ completionIntegers X v := (residueSectionIntegers X v a).property

/-- A family is a system of residue representatives modulo a uniformizer. -/
def IsResidueReps (v : closedPoints X.left) (π : (completion X v)ˣ)
    (reps : X.left.residueField v.1 → completion X v) : Prop :=
  (∀ a, reps a ∈ completionIntegers X v) ∧
    ∀ a, Valued.v (reps a - residueRep X v a) ≤ Valued.v π.val

/-- The predicate for residue representatives unfolds to its defining conditions. -/
theorem isResidueReps_iff (v : closedPoints X.left) (π : (completion X v)ˣ)
    (reps : X.left.residueField v.1 → completion X v) :
    IsResidueReps X v π reps ↔
      (∀ a, reps a ∈ completionIntegers X v) ∧
        ∀ a, Valued.v (reps a - residueRep X v a) ≤ Valued.v π.val := Iff.rfl

/-- The canonical residue representatives form a residue-representative system. -/
theorem residueRep_isResidueReps (v : closedPoints X.left)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val) :
    IsResidueReps X v π (residueRep X v) := by
  refine ⟨residueRep_mem_integers X v, ?_⟩
  intro a
  simp only [sub_self, map_zero]
  exact zero_le

/-- The central inverse-uniformizer matrix in the adelic general linear group. -/
def heckeUMatrix (v : closedPoints X.left) (π : (completion X v)ˣ) :
    GL (Fin 2) (adeleRing X) :=
  GeneralLinearGroup.scalar (Fin 2) (localAdeleUnit X v π)⁻¹

/-- The central Hecke matrix is the scalar inverse of the local idèle. -/
theorem heckeUMatrix_spec (v : closedPoints X.left) (π : (completion X v)ˣ) :
    heckeUMatrix X v π = GeneralLinearGroup.scalar (Fin 2) (localAdeleUnit X v π)⁻¹ := rfl

omit [Fintype k] in
/-- The diagonal adelic representative for the `T` operator. -/
def heckeTDiag (v : closedPoints X.left) (π : (completion X v)ˣ) :
    GL (Fin 2) (adeleRing X) := localGL X v (heckeDiag X v π)

omit [Fintype k] in
/-- The diagonal operator is represented by the explicit local diagonal matrix. -/
theorem heckeTDiag_spec (v : closedPoints X.left) (π : (completion X v)ˣ) :
    (heckeTDiag X v π).val =
      localMatrix X v (Matrix.diagonal (fun i : Fin 2 ↦ if i = 0 then π.inv else 1)) := rfl

omit [Fintype k] in
/-- The lower-triangular adelic representative for a residue class in `T`. -/
def heckeTOff (v : closedPoints X.left) (π : (completion X v)ˣ)
    (lval : completion X v) : GL (Fin 2) (adeleRing X) :=
  localGL X v (heckeUnip X v π lval)

omit [Fintype k] in
/-- The off-diagonal operator is represented by the explicit local triangular matrix. -/
theorem heckeTOff_spec (v : closedPoints X.left) (π : (completion X v)ˣ)
    (lval : completion X v) :
    (heckeTOff X v π lval).val =
      localMatrix X v !![1, 0; -π.inv * lval, π.inv] := rfl

/-- Scalar multiplication preserves the invariance and cuspidality conditions. -/
theorem UnramifiedCuspForm.smul_mem (a : Λ) (φ : UnramifiedCuspForm X Λ) :
    IsRightInvariant X (fun x ↦ a * φ.toFun x) ∧
      IsLeftInvariant X (fun x ↦ a * φ.toFun x) ∧
        IsCuspidal X (fun x ↦ a * φ.toFun x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x γ
    exact congrArg (a * ·) (φ.right_inv x γ)
  · intro u x
    exact congrArg (a * ·) (φ.left_inv u x)
  · intro x
    obtain ⟨U, s, hU, hs, hsum⟩ := φ.cuspidal x
    refine ⟨U, s, ?_, hs, ?_⟩
    · intro z u hu
      exact congrArg (a * ·) (hU z u hu)
    · change ∑ z ∈ s, a * φ.toFun (x * GeneralLinearGroup.upperRightHom z) = 0
      rw [← Finset.mul_sum, hsum, mul_zero]

/-- Scale an unramified cusp form pointwise by a coefficient. -/
def UnramifiedCuspForm.smul (a : Λ) (φ : UnramifiedCuspForm X Λ) : UnramifiedCuspForm X Λ :=
  UnramifiedCuspForm.of X (fun x ↦ a * φ.toFun x)
    (UnramifiedCuspForm.smul_mem X a φ).1
    (UnramifiedCuspForm.smul_mem X a φ).2.1
    (UnramifiedCuspForm.smul_mem X a φ).2.2

/-- The scaled cusp form evaluates pointwise as coefficient multiplication. -/
theorem UnramifiedCuspForm.smul_toFun (a : Λ) (φ : UnramifiedCuspForm X Λ) :
    (UnramifiedCuspForm.smul X a φ).toFun = fun x ↦ a * φ.toFun x := rfl

/-- The central `U` translation preserves cusp-form conditions. -/
theorem heckeU_mem (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ) :
    IsRightInvariant X (fun x ↦ φ.toFun (heckeUMatrix X v (uniformizer X v) * x)) ∧
      IsLeftInvariant X (fun x ↦ φ.toFun (heckeUMatrix X v (uniformizer X v) * x)) ∧
        IsCuspidal X (fun x ↦ φ.toFun (heckeUMatrix X v (uniformizer X v) * x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x γ
    simpa only [mul_assoc] using
      φ.right_inv (heckeUMatrix X v (uniformizer X v) * x) γ
  · intro u x
    change φ.toFun (heckeUMatrix X v (uniformizer X v) * (integerAdeleGL X u * x)) = _
    rw [← mul_assoc, heckeUMatrix, GeneralLinearGroup.scalar_commute, mul_assoc]
    exact φ.left_inv u _
  · intro x
    simpa only [mul_assoc] using
      φ.cuspidal (heckeUMatrix X v (uniformizer X v) * x)

/-- The unramified `U` operator. -/
def heckeU (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ) :
    UnramifiedCuspForm X Λ :=
  UnramifiedCuspForm.of X (fun x ↦ φ.toFun (heckeUMatrix X v (uniformizer X v) * x))
    (heckeU_mem X v φ).1 (heckeU_mem X v φ).2.1 (heckeU_mem X v φ).2.2

private theorem heckeUMatrix_change_uniformizer (v : closedPoints X.left)
    (π π' : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (hπ' : IsUniformizer X v π'.val) :
    ∃ u : GL (Fin 2) (integerAdeleRing X),
      heckeUMatrix X v π = integerAdeleGL X u * heckeUMatrix X v π' := by
  have hint (p q : (completion X v)ˣ) (hp : IsUniformizer X v p.val)
      (hq : IsUniformizer X v q.val) (w : closedPoints X.left) :
      localAdele X v p.inv w * localAdele X v q.val w ∈ completionIntegers X w := by
    by_cases hw : w = v
    · subst w
      change Valued.v (localAdele X v p.inv v * localAdele X v q.val v) ≤ 1
      rw [localAdele, localAdele, RestrictedProduct.mulSingle_eq_same,
        RestrictedProduct.mulSingle_eq_same, map_mul,
        show p.inv = p.val⁻¹ from Units.val_inv_eq_inv_val p,
        Valuation.map_inv, hp, hq]
      simp
    · simpa only [localAdele, RestrictedProduct.mulSingle_eq_of_ne _ _ hw, one_mul]
        using (completionIntegers X w).one_mem
  let r := (localAdeleUnit X v π)⁻¹ * localAdeleUnit X v π'
  let a : (integerAdeleRing X)ˣ :=
    { val := fun w ↦ ⟨r.val w, hint π π' hπ hπ' w⟩
      inv := fun w ↦ ⟨r.inv w, hint π' π hπ' hπ w⟩
      val_inv := by
        funext w
        apply Subtype.ext
        exact congrArg (fun z : adeleRing X ↦ z w) r.val_inv
      inv_val := by
        funext w
        apply Subtype.ext
        exact congrArg (fun z : adeleRing X ↦ z w) r.inv_val }
  have ha : Units.map (integerAdeleRing.toAdeleRing X) a = r := by
    apply Units.ext
    apply RestrictedProduct.ext
    intro w
    rfl
  refine ⟨GeneralLinearGroup.scalar (Fin 2) a, ?_⟩
  change GeneralLinearGroup.scalar (Fin 2) (localAdeleUnit X v π)⁻¹ =
    GeneralLinearGroup.map (integerAdeleRing.toAdeleRing X)
      (GeneralLinearGroup.scalar (Fin 2) a) *
        GeneralLinearGroup.scalar (Fin 2) (localAdeleUnit X v π')⁻¹
  rw [GeneralLinearGroup.map_scalar, ha, ← map_mul]
  congr 1
  simp [r, mul_assoc]

/-- The `U` operator evaluates by translation by any uniformizer matrix. -/
theorem heckeU_spec (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (x : GL (Fin 2) (adeleRing X)) :
    (heckeU X v φ).toFun x = φ.toFun (heckeUMatrix X v π * x) := by
  obtain ⟨u, hu⟩ := heckeUMatrix_change_uniformizer X v (uniformizer X v) π
    (uniformizer_isUniformizer X v) hπ
  change φ.toFun (heckeUMatrix X v (uniformizer X v) * x) = _
  rw [hu, mul_assoc]
  exact φ.left_inv u _

/-- The `U` translation is independent of the chosen uniformizer. -/
theorem heckeU_independent (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π π' : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (hπ' : IsUniformizer X v π'.val) (x : GL (Fin 2) (adeleRing X)) :
    φ.toFun (heckeUMatrix X v π * x) = φ.toFun (heckeUMatrix X v π' * x) := by
  obtain ⟨u, hu⟩ := heckeUMatrix_change_uniformizer X v π π' hπ hπ'
  rw [hu, mul_assoc]
  exact φ.left_inv u _

/-- The finite-sum `T` translation preserves cusp-form conditions. -/
theorem heckeT_mem (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ) :
    IsRightInvariant X (fun x ↦ φ.toFun (heckeTDiag X v (uniformizer X v) * x) +
      ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v (uniformizer X v) (residueRep X v a) * x)) ∧
      IsLeftInvariant X (fun x ↦ φ.toFun (heckeTDiag X v (uniformizer X v) * x) +
      ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v (uniformizer X v) (residueRep X v a) * x)) ∧
        IsCuspidal X (fun x ↦ φ.toFun (heckeTDiag X v (uniformizer X v) * x) +
      ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v (uniformizer X v) (residueRep X v a) * x)) := sorry

/-- The finite-sum unramified `T` operator. -/
def heckeT (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ) :
    UnramifiedCuspForm X Λ :=
  UnramifiedCuspForm.of X
    (fun x ↦ φ.toFun (heckeTDiag X v (uniformizer X v) * x) +
      ∑ a : X.left.residueField v.1,
        φ.toFun (heckeTOff X v (uniformizer X v) (residueRep X v a) * x))
    (heckeT_mem X v φ).1 (heckeT_mem X v φ).2.1 (heckeT_mem X v φ).2.2

private theorem unramified_translate_eq_of_integral (φ : UnramifiedCuspForm X Λ)
    (g h : GL (Fin 2) (adeleRing X))
    (hg : ∀ i j w, ((g * h⁻¹).val i j) w ∈ completionIntegers X w)
    (hh : ∀ i j w, ((h * g⁻¹).val i j) w ∈ completionIntegers X w)
    (x : GL (Fin 2) (adeleRing X)) : φ.toFun (g * x) = φ.toFun (h * x) := by
  let a := g * h⁻¹
  let m : Matrix (Fin 2) (Fin 2) (integerAdeleRing X) :=
    fun i j w ↦ ⟨a.val i j w, hg i j w⟩
  let n : Matrix (Fin 2) (Fin 2) (integerAdeleRing X) :=
    fun i j w ↦ ⟨a.inv i j w, hh i j w⟩
  have hm : m.map (integerAdeleRing.toAdeleRing X) = a.val := by
    apply Matrix.ext
    intro i j
    apply RestrictedProduct.ext
    intro w
    rfl
  have hn : n.map (integerAdeleRing.toAdeleRing X) = a.inv := by
    apply Matrix.ext
    intro i j
    apply RestrictedProduct.ext
    intro w
    rfl
  have hinj : Function.Injective (integerAdeleRing.toAdeleRing X) := by
    intro b c hbc
    funext w
    apply Subtype.ext
    exact congrArg (fun z : adeleRing X ↦ z w) hbc
  let u : GL (Fin 2) (integerAdeleRing X) :=
    { val := m
      inv := n
      val_inv := by
        apply Matrix.map_injective hinj
        simpa only [Matrix.map_mul, hm, hn, Matrix.map_one, map_zero, map_one]
          using a.val_inv
      inv_val := by
        apply Matrix.map_injective hinj
        simpa only [Matrix.map_mul, hm, hn, Matrix.map_one, map_zero, map_one]
          using a.inv_val }
  have hu : integerAdeleGL X u = a := Units.ext hm
  calc
    φ.toFun (g * x) = φ.toFun (integerAdeleGL X u * (h * x)) := by
      rw [hu]
      simp [a, mul_assoc]
    _ = φ.toFun (h * x) := φ.left_inv u _

private theorem unramified_local_translate_eq (v : closedPoints X.left)
    (φ : UnramifiedCuspForm X Λ) (g h : GL (Fin 2) (completion X v))
    (hg : ∀ i j, (g.val * h.inv) i j ∈ completionIntegers X v)
    (hh : ∀ i j, (h.val * g.inv) i j ∈ completionIntegers X v)
    (x : GL (Fin 2) (adeleRing X)) :
    φ.toFun (localGL X v g * x) = φ.toFun (localGL X v h * x) := by
  have hself (g h : GL (Fin 2) (completion X v)) (i j : Fin 2) :
      ((localGL X v g * (localGL X v h)⁻¹).val i j) v = (g.val * h.inv) i j := by
    fin_cases i <;> fin_cases j <;>
      simp [localGL, localMatrix, localAdele, localAdeleZero,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hoff (g h : GL (Fin 2) (completion X v)) (i j : Fin 2)
      (w : closedPoints X.left) (hw : w ≠ v) :
      ((localGL X v g * (localGL X v h)⁻¹).val i j) w =
        (1 : Matrix (Fin 2) (Fin 2) (completion X w)) i j := by
    fin_cases i <;> fin_cases j <;>
      simp [localGL, localMatrix, localAdele, localAdeleZero,
        Matrix.mul_apply, Fin.sum_univ_two,
        RestrictedProduct.mulSingle_eq_of_ne _ _ hw,
        RestrictedProduct.single_eq_of_ne _ _ hw]
  apply unramified_translate_eq_of_integral X φ
  · intro i j w
    by_cases hw : w = v
    · subst w
      rw [hself]
      exact hg i j
    · rw [hoff _ _ _ _ _ hw]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · intro i j w
    by_cases hw : w = v
    · subst w
      rw [hself]
      exact hh i j
    · rw [hoff _ _ _ _ _ hw]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem inv_mul_mem_completionIntegers (v : closedPoints X.left)
    (π : (completion X v)ˣ) (a : completion X v) (ha : Valued.v a ≤ Valued.v π.val) :
    π.inv * a ∈ completionIntegers X v := by
  change Valued.v (π.inv * a) ≤ 1
  rw [map_mul, show π.inv = π.val⁻¹ from Units.val_inv_eq_inv_val π, Valuation.map_inv]
  calc
    (Valued.v π.val)⁻¹ * Valued.v a ≤ (Valued.v π.val)⁻¹ * Valued.v π.val :=
      mul_le_mul_left' ha _
    _ = 1 := inv_mul_cancel₀ (Valuation.ne_zero_iff _ |>.2 π.ne_zero)

/-- The `T` operator evaluates by its diagonal and residue-indexed translations. -/
theorem heckeT_spec (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (reps : X.left.residueField v.1 → completion X v)
    (hreps : IsResidueReps X v π reps) (x : GL (Fin 2) (adeleRing X)) :
    (heckeT X v φ).toFun x = φ.toFun (heckeTDiag X v π * x) +
      ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v π (reps a) * x) := by
  have hdiag (p q : (completion X v)ˣ) (hpq : Valued.v q.val = Valued.v p.val) :
      ∀ i j, ((heckeDiag X v p).val * (heckeDiag X v q).inv) i j ∈
        completionIntegers X v := by
    have hd := inv_mul_mem_completionIntegers X v p q.val hpq.le
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [heckeDiag, Matrix.mul_apply, Fin.sum_univ_two] using hd
    · simp [heckeDiag, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [heckeDiag, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [heckeDiag, Matrix.mul_apply, Fin.sum_univ_two]
  have hoff (p q : (completion X v)ˣ) (r s : completion X v)
      (hpq : Valued.v q.val = Valued.v p.val)
      (hrs : Valued.v (s - r) ≤ Valued.v p.val) :
      ∀ i j, ((heckeUnip X v p r).val * (heckeUnip X v q s).inv) i j ∈
        completionIntegers X v := by
    have hd := inv_mul_mem_completionIntegers X v p q.val hpq.le
    have hc := inv_mul_mem_completionIntegers X v p (s - r) hrs
    have hmul : (heckeUnip X v p r).val * (heckeUnip X v q s).inv =
        !![1, 0; p.inv * (s - r), p.inv * q.val] := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [heckeUnip, Matrix.mul_apply, Fin.sum_univ_two]
      all_goals ring
    rw [hmul]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using (completionIntegers X v).one_mem
    · simpa using (completionIntegers X v).zero_mem
    · simpa using hc
    · simpa using hd
  have hv : Valued.v π.val = Valued.v (uniformizer X v).val :=
    hπ.trans (uniformizer_isUniformizer X v).symm
  change φ.toFun (heckeTDiag X v (uniformizer X v) * x) +
    ∑ a, φ.toFun (heckeTOff X v (uniformizer X v) (residueRep X v a) * x) = _
  apply congrArg₂ (· + ·)
  · exact unramified_local_translate_eq X v φ _ _ (hdiag _ _ hv) (hdiag _ _ hv.symm) x
  · apply Finset.sum_congr rfl
    intro a ha
    apply unramified_local_translate_eq X v φ
    · apply hoff _ _ _ _ hv
      exact (hreps.2 a).trans_eq hv
    · apply hoff _ _ _ _ hv.symm
      rw [Valuation.map_sub_swap]
      exact hreps.2 a

/-- The finite-sum `T` operator is independent of uniformizers and representatives. -/
theorem heckeT_independent (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π π' : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (hπ' : IsUniformizer X v π'.val)
    (reps reps' : X.left.residueField v.1 → completion X v)
    (hreps : IsResidueReps X v π reps) (hreps' : IsResidueReps X v π' reps')
    (x : GL (Fin 2) (adeleRing X)) :
    φ.toFun (heckeTDiag X v π * x) + ∑ a, φ.toFun (heckeTOff X v π (reps a) * x) =
      φ.toFun (heckeTDiag X v π' * x) + ∑ a, φ.toFun (heckeTOff X v π' (reps' a) * x) := by
  exact (heckeT_spec X v φ π hπ reps hreps x).symm.trans
    (heckeT_spec X v φ π' hπ' reps' hreps' x)

/-- An unramified cusp form is an eigenform for the Hecke system `f`. -/
def IsEigenform (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ) : Prop :=
  (∃ x, IsUnit (φ.toFun x)) ∧
    (∀ v, heckeT X v φ = UnramifiedCuspForm.smul X (f.t v) φ) ∧
    (∀ v, heckeU X v φ = UnramifiedCuspForm.smul X (f.u v).val φ)

/-- The eigenform predicate is equivalent to its nonvanishing and two eigen-equations. -/
theorem isEigenform_iff (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ) :
    IsEigenform X φ f ↔
      (∃ x, IsUnit (φ.toFun x)) ∧
        (∀ v, heckeT X v φ = UnramifiedCuspForm.smul X (f.t v) φ) ∧
        (∀ v, heckeU X v φ = UnramifiedCuspForm.smul X (f.u v).val φ) := Iff.rfl

/-- The nonvanishing condition in the definition of an eigenform. -/
theorem isEigenform_isUnit (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ)
    (hφ : IsEigenform X φ f) : ∃ x, IsUnit (φ.toFun x) := hφ.1

/-- The `T` eigen-equation of an unramified cusp eigenform. -/
theorem isEigenform_heckeT (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ)
    (hφ : IsEigenform X φ f) (v : closedPoints X.left) :
    heckeT X v φ = UnramifiedCuspForm.smul X (f.t v) φ := hφ.2.1 v

/-- The `U` eigen-equation of an unramified cusp eigenform. -/
theorem isEigenform_heckeU (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ)
    (hφ : IsEigenform X φ f) (v : closedPoints X.left) :
    heckeU X v φ = UnramifiedCuspForm.smul X (f.u v).val φ := hφ.2.2 v

end AlgebraicGeometry.SchemeOverField
