/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.Splitting.Criterion
public import ReasLib.Algebra.CentralSimple.Splitting.MaximalSubfield
public import Mathlib.FieldTheory.JacobsonNoether

/-! # Separable Splitting Fields for Central Simple Algebras

Every finite central simple algebra admits a finite separable splitting field.
This is deduced from the existence of separable maximal subfields in the
division-algebra representative (Proposition 11.8.5).

## Main declarations

- `CSA.exists_separable_maximalSubfield` — separable maximal subfield exists in a division algebra
- `CSA.exists_finite_separable_splitting_field` — representative-level existence
- `BrauerGroup.IsSplitBy` — Brauer-class splitting predicate
- `BrauerGroup.isSplitBy_mk` — simp lemma reducing class splitting to representative splitting
- `BrauerGroup.exists_finite_separable_splitting_field` — class-level existence

## References

- [Stacks Project, Tag 0752](https://stacks.math.columbia.edu/tag/0752)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

section

open JacobsonNoether
open Subalgebra
open scoped IntermediateField

variable {k : Type u} [Field k]
variable {D : Type v} [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
  [Algebra.IsCentral k D]

omit [FiniteDimensional k D] [Algebra.IsCentral k D] in
private lemma inv_mem_centralizer_of_mem_centralizer (K : Subalgebra k D) {x : D}
    (hx : x ∈ Subalgebra.centralizer k (K : Set D)) :
    x⁻¹ ∈ Subalgebra.centralizer k (K : Set D) := by
  rw [Subalgebra.mem_centralizer_iff] at hx ⊢
  intro y hy
  by_cases hx0 : x = 0
  · simp [hx0]
  · calc
      y * x⁻¹ = (x⁻¹ * x) * y * x⁻¹ := by rw [inv_mul_cancel₀ hx0, one_mul]
      _ = x⁻¹ * (x * y) * x⁻¹ := by simp [mul_assoc]
      _ = x⁻¹ * (y * x) * x⁻¹ := by rw [hx y hy]
      _ = x⁻¹ * y * (x * x⁻¹) := by simp [mul_assoc]
      _ = x⁻¹ * y := by rw [mul_inv_cancel₀ hx0, mul_one]

omit [Algebra.IsCentral k D] in
private lemma exists_finrank_maximal_separable_subfield :
    ∃ K : Subalgebra k D, IsField K ∧ Algebra.IsSeparable k K ∧
      ∀ L : Subalgebra k D, IsField L → Algebra.IsSeparable k L →
        Module.finrank k L ≤ Module.finrank k K := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ K : Subalgebra k D, IsField K ∧ Algebra.IsSeparable k K ∧ Module.finrank k K = n
  have hbotField : IsField (⊥ : Subalgebra k D) := by
    exact (Algebra.botEquiv k D).toMulEquiv.isField (Field.toIsField k)
  have hbotSep : Algebra.IsSeparable k (⊥ : Subalgebra k D) := by
    exact (AlgEquiv.Algebra.isSeparable_iff (Algebra.botEquiv k D)).2 inferInstance
  have hP : P 1 := by
    refine ⟨⊥, hbotField, hbotSep, ?_⟩
    simpa using (Subalgebra.finrank_bot : Module.finrank k (⊥ : Subalgebra k D) = 1)
  let n := Nat.findGreatest P (Module.finrank k D)
  have hnP : P n := by
    have hone : 1 ≤ Module.finrank k D := by
      have hbot := Submodule.finrank_le (Subalgebra.toSubmodule (⊥ : Subalgebra k D))
      simpa [Subalgebra.finrank_bot] using hbot
    exact Nat.findGreatest_spec hone hP
  rcases hnP with ⟨K, hKfield, hKsep, hKn⟩
  refine ⟨K, hKfield, hKsep, ?_⟩
  intro L hLfield hLsep
  have hbound : Module.finrank k L ≤ Module.finrank k D := by
    simpa using Submodule.finrank_le (Subalgebra.toSubmodule L)
  have hLn : Module.finrank k L ≤ n := Nat.le_findGreatest hbound ⟨L, hLfield, hLsep, rfl⟩
  omega

omit [FiniteDimensional k D] [Algebra.IsCentral k D] in
private lemma self_le_centralizer_of_isField
    (K : Subalgebra k D) (hKfield : IsField K) :
    K ≤ Subalgebra.centralizer k (K : Set D) := by
  intro x hx
  rw [Subalgebra.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hKfield.mul_comm ⟨y, hy⟩ ⟨x, hx⟩)

private noncomputable def centralizerSubfieldInclusion
    (K : Subalgebra k D) (hKfield : IsField K) :
    K →ₐ[k] Subalgebra.centralizer k (K : Set D) :=
  Subalgebra.inclusion (self_le_centralizer_of_isField (k := k) (D := D) K hKfield)

@[reducible]
private noncomputable def centralizerAlgebra
    (K : Subalgebra k D) (hKfield : IsField K) :
    letI : Field K := hKfield.toField
    Algebra K (Subalgebra.centralizer k (K : Set D)) :=
  letI : Field K := hKfield.toField
  (centralizerSubfieldInclusion (k := k) (D := D) K hKfield).toRingHom.toAlgebra'
    fun c z ↦ Subtype.ext ((Subalgebra.mem_centralizer_iff (R := k)).mp z.2 c.1 c.2)

private lemma centralizer_isCentral_over_subfield
    (K : Subalgebra k D) (hKfield : IsField K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    Algebra.IsCentral K (Subalgebra.centralizer k (K : Set D)) := by
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  have hCC :
      Subalgebra.centralizer k ((Subalgebra.centralizer k (K : Set D) : Subalgebra k D) : Set D)
        = K := by
    simpa using
      (Subalgebra.centralizer_centralizer_eq (k := k) (A := CSA.mk (AlgCat.of k D)) (B := K))
  refine ⟨fun x hx ↦ ?_⟩
  have hxC :
      x.1 ∈
        Subalgebra.centralizer k
          ((Subalgebra.centralizer k (K : Set D) : Subalgebra k D) : Set D) := by
    rw [Subalgebra.mem_centralizer_iff]
    rw [Subalgebra.mem_center_iff] at hx
    intro y hy
    exact congrArg Subtype.val (hx ⟨y, hy⟩)
  have hxK : x.1 ∈ K := by
    rw [hCC] at hxC
    exact hxC
  rw [Algebra.mem_bot]
  exact ⟨⟨x.1, hxK⟩, rfl⟩

omit [FiniteDimensional k D] [Algebra.IsCentral k D] in
private lemma centralizer_bot_ne_top_of_nontrivial
    (K : Subalgebra k D) (hKfield : IsField K)
    (hCK : Subalgebra.centralizer k (K : Set D) ≠ K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    (⊥ : Subalgebra K (Subalgebra.centralizer k (K : Set D))) ≠ ⊤ := by
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  have hlt : K < Subalgebra.centralizer k (K : Set D) := by
    exact lt_of_le_of_ne
      (self_le_centralizer_of_isField (k := k) (D := D) K hKfield) hCK.symm
  rcases SetLike.exists_of_lt hlt with ⟨x, hxC, hxK⟩
  intro hbot
  have hxbot :
      (⟨x, hxC⟩ : Subalgebra.centralizer k (K : Set D)) ∈
        (⊥ : Subalgebra K (Subalgebra.centralizer k (K : Set D))) := by
    rw [hbot]
    exact Algebra.mem_top
  rw [Algebra.mem_bot] at hxbot
  rcases hxbot with ⟨a, ha⟩
  apply hxK
  have hxa : (a : D) = x := congrArg Subtype.val ha
  rw [← hxa]
  exact a.2

private noncomputable def adjoinRootLiftOfAeval {R : Type u} [CommRing R] {S : Type v} [Ring S]
    [Algebra R S] (p : Polynomial R) (x : S) (hx : Polynomial.aeval x p = 0) :
    AdjoinRoot p →ₐ[R] S :=
  Ideal.Quotient.liftₐ (Ideal.span {p}) (Polynomial.aeval x) fun g hg ↦ by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hg
    rw [map_mul, hx, zero_mul]

private lemma adjoinRootLiftOfAeval_root {R : Type u} [CommRing R] {S : Type v} [Ring S]
    [Algebra R S] (p : Polynomial R) (x : S) (hx : Polynomial.aeval x p = 0) :
    adjoinRootLiftOfAeval p x hx (AdjoinRoot.root p) = x := by
  exact Polynomial.aeval_X x

private noncomputable def adjoinRootToAmbient_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    (x : Subalgebra.centralizer k (K : Set D)) → AdjoinRoot (minpoly K x) →ₐ[k] D :=
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  letI : IsScalarTower k K (Subalgebra.centralizer k (K : Set D)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  fun x ↦
    (Subalgebra.centralizer k (K : Set D)).val.comp <|
      AlgHom.restrictScalars k <|
        adjoinRootLiftOfAeval (minpoly K x) x (minpoly.aeval K x)

omit [FiniteDimensional k D] [Algebra.IsCentral k D] in
private lemma adjoinRootToAmbient_of_centralizer_element_root
    (K : Subalgebra k D) (hKfield : IsField K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    ∀ x : Subalgebra.centralizer k (K : Set D),
      adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x
          (AdjoinRoot.root (minpoly K x)) = x.1 := by
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  intro x
  simp [adjoinRootToAmbient_of_centralizer_element, adjoinRootLiftOfAeval_root]

omit [FiniteDimensional k D] [Algebra.IsCentral k D] in
private lemma subfield_le_adjoinRoot_range_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    ∀ x : Subalgebra.centralizer k (K : Set D),
      K ≤ (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  intro x a ha
  let a' : K := ⟨a, ha⟩
  refine ⟨algebraMap K (AdjoinRoot (minpoly K x)) a', ?_⟩
  have h := (adjoinRootLiftOfAeval (minpoly K x) x (minpoly.aeval K x)).commutes a'
  calc (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x)
        (algebraMap K (AdjoinRoot (minpoly K x)) a')
      = ((adjoinRootLiftOfAeval (minpoly K x) x (minpoly.aeval K x))
          (algebraMap K (AdjoinRoot (minpoly K x)) a') : D) := rfl
    _ = a := by
          rw [h]
          rfl

omit [FiniteDimensional k D] [Algebra.IsCentral k D] in
private lemma centralizer_element_mem_adjoinRoot_range_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    ∀ x : Subalgebra.centralizer k (K : Set D),
      x.1 ∈ (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  intro x
  refine ⟨AdjoinRoot.root (minpoly K x), ?_⟩
  exact adjoinRootToAmbient_of_centralizer_element_root (k := k) (D := D) K hKfield x

omit [FiniteDimensional k D] [Algebra.IsCentral k D] in
private lemma adjoinRoot_range_strict_of_nontrivial_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    ∀ x : Subalgebra.centralizer k (K : Set D),
      x ∉ (⊥ : Subalgebra K (Subalgebra.centralizer k (K : Set D))) →
      K < (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range := by
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  intro x hx
  refine lt_of_le_of_ne
    (subfield_le_adjoinRoot_range_of_centralizer_element (k := k) (D := D) K hKfield x) ?_
  intro hEq
  have hxrange :
      x.1 ∈ (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range :=
    centralizer_element_mem_adjoinRoot_range_of_centralizer_element
      (k := k) (D := D) K hKfield x
  have hxK : x.1 ∈ K := by
    simpa [hEq] using hxrange
  apply hx
  rw [Algebra.mem_bot]
  exact ⟨⟨x.1, hxK⟩, rfl⟩

omit [Algebra.IsCentral k D] in
private lemma finiteDimensional_centralizer_over_subfield
    (K : Subalgebra k D) (hKfield : IsField K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    FiniteDimensional K (Subalgebra.centralizer k (K : Set D)) := by
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  letI : FiniteDimensional k K :=
    FiniteDimensional.of_injective K.val.toLinearMap Subtype.val_injective
  letI : FiniteDimensional K D := FiniteDimensional.right k K D
  let iCD : Subalgebra.centralizer k (K : Set D) →ₗ[K] D :=
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact FiniteDimensional.of_injective iCD fun x y hxy ↦ Subtype.ext hxy

private noncomputable def adjoinRoot_range_algEquiv_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    (x : Subalgebra.centralizer k (K : Set D)) →
      AdjoinRoot (minpoly K x) ≃ₐ[k]
        (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range :=
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  letI : FiniteDimensional K (Subalgebra.centralizer k (K : Set D)) :=
    finiteDimensional_centralizer_over_subfield (k := k) (D := D) K hKfield
  letI : Algebra.IsAlgebraic K (Subalgebra.centralizer k (K : Set D)) :=
    Algebra.IsAlgebraic.of_finite K _
  fun x ↦
    letI : Fact (Irreducible (minpoly K x)) :=
      ⟨minpoly.irreducible (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral⟩
    AlgEquiv.ofInjectiveField
      (adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x)

omit [Algebra.IsCentral k D] in
private lemma adjoinRoot_range_isField_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    ∀ x : Subalgebra.centralizer k (K : Set D),
      IsField
        ((adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range) := by
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  letI : FiniteDimensional K (Subalgebra.centralizer k (K : Set D)) :=
    finiteDimensional_centralizer_over_subfield (k := k) (D := D) K hKfield
  letI : Algebra.IsAlgebraic K (Subalgebra.centralizer k (K : Set D)) :=
    Algebra.IsAlgebraic.of_finite K _
  intro x
  letI : Fact (Irreducible (minpoly K x)) :=
    ⟨minpoly.irreducible (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral⟩
  exact (adjoinRoot_range_algEquiv_of_centralizer_element
      (k := k) (D := D) K hKfield x).symm.toMulEquiv.isField
    (Field.toIsField (AdjoinRoot (minpoly K x)))

omit [Algebra.IsCentral k D] in
private lemma adjoinRoot_range_isSeparable_of_centralizer_element
    (K : Subalgebra k D) (hKfield : IsField K) (hKsep : Algebra.IsSeparable k K) :
    letI : Field K := hKfield.toField
    letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
      centralizerAlgebra (k := k) (D := D) K hKfield
    ∀ x : Subalgebra.centralizer k (K : Set D), IsSeparable K x →
      Algebra.IsSeparable k
        ((adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range) := by
  letI : Field K := hKfield.toField
  letI : Algebra K (Subalgebra.centralizer k (K : Set D)) :=
    centralizerAlgebra (k := k) (D := D) K hKfield
  intro x hxsep
  let e := adjoinRoot_range_algEquiv_of_centralizer_element (k := k) (D := D) K hKfield x
  have hxint : IsIntegral K x := IsSeparable.isIntegral hxsep
  letI : Fact (Irreducible (minpoly K x)) := ⟨minpoly.irreducible hxint⟩
  let y : AdjoinRoot (minpoly K x) := AdjoinRoot.root (minpoly K x)

  have hysep : IsSeparable K y := by
    simpa [y, IsSeparable, AdjoinRoot.minpoly_root (minpoly.ne_zero hxint), minpoly.monic hxint]
      using hxsep
  have hsimple : Algebra.IsSeparable K K⟮y⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := AdjoinRoot (minpoly K x))).2 hysep
  have htop : K⟮y⟯ = ⊤ := IntermediateField.adjoin_root_eq_top (p := minpoly K x)
  have hsourceK : Algebra.IsSeparable K (AdjoinRoot (minpoly K x)) := by
    have hsourceTop :
        Algebra.IsSeparable K (⊤ : IntermediateField K (AdjoinRoot (minpoly K x))) :=
      AlgEquiv.Algebra.isSeparable (IntermediateField.equivOfEq htop)
    exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv :
      (⊤ : IntermediateField K (AdjoinRoot (minpoly K x))) ≃ₐ[K] AdjoinRoot (minpoly K x))
  letI : Algebra.IsSeparable K (AdjoinRoot (minpoly K x)) := hsourceK
  letI : IsScalarTower k K (AdjoinRoot (minpoly K x)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra.IsSeparable k (AdjoinRoot (minpoly K x)) :=
    Algebra.IsSeparable.trans k K (AdjoinRoot (minpoly K x))
  exact AlgEquiv.Algebra.isSeparable e

private lemma exists_larger_separable_subfield_of_nontrivial_centralizer
    (K : Subalgebra k D) (hKfield : IsField K) (hKsep : Algebra.IsSeparable k K)
    (hCK : Subalgebra.centralizer k (K : Set D) ≠ K) :
    ∃ L : Subalgebra k D, IsField L ∧ Algebra.IsSeparable k L ∧ K < L := by
  classical
  let C := Subalgebra.centralizer k (K : Set D)
  have hKC : K ≤ C := self_le_centralizer_of_isField (k := k) (D := D) K hKfield
  letI : Field K := hKfield.toField
  letI : Algebra K C := centralizerAlgebra (k := k) (D := D) K hKfield
  let C₀ : Subfield D :=
    C.toSubring.toSubfield fun x hx ↦
      inv_mem_centralizer_of_mem_centralizer (k := k) (D := D) K hx
  let iKC₀ : K →+* C₀ :=
    { toFun := fun a ↦ ⟨a.1, hKC a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  letI : Algebra K C₀ := iKC₀.toAlgebra' fun c z ↦
    Subtype.ext ((Subalgebra.mem_centralizer_iff k).1 (show z.1 ∈ C from z.2) c.1 c.2)
  letI : FiniteDimensional k K :=
    FiniteDimensional.of_injective K.val.toLinearMap Subtype.val_injective
  letI : FiniteDimensional K D := FiniteDimensional.right k K D
  let iC₀D : C₀ →ₗ[K] D :=
    { toFun := Subtype.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  letI : FiniteDimensional K C₀ :=
    FiniteDimensional.of_injective iC₀D fun x y hxy ↦ Subtype.ext hxy
  letI : Algebra.IsAlgebraic K C₀ := Algebra.IsAlgebraic.of_finite K C₀

  have hCproper₀ : (⊥ : Subalgebra K C₀) ≠ ⊤ := by
    intro hbot
    have hEq : C = K := by
      apply le_antisymm
      · intro x hx
        have hxbot : (⟨x, hx⟩ : C₀) ∈ (⊥ : Subalgebra K C₀) := by
          rw [hbot]
          exact Algebra.mem_top
        rw [Algebra.mem_bot] at hxbot
        rcases hxbot with ⟨a, ha⟩
        have hxa : (a : D) = x := congrArg Subtype.val ha
        rw [← hxa]
        exact a.2
      · exact hKC
    exact hCK hEq
  letI : Algebra.IsCentral K C₀ := by
    have hCC : Subalgebra.centralizer k (C : Set D) = K := by
      simpa [C] using
        (Subalgebra.centralizer_centralizer_eq (k := k) (A := CSA.mk (AlgCat.of k D)) (B := K))
    refine ⟨fun x hx ↦ ?_⟩
    have hxC : x.1 ∈ Subalgebra.centralizer k (C : Set D) := by
      rw [Subalgebra.mem_centralizer_iff]
      rw [Subalgebra.mem_center_iff] at hx
      intro y hy
      exact congrArg Subtype.val (hx ⟨y, hy⟩)
    have hxK : x.1 ∈ K := by
      rw [hCC] at hxC
      exact hxC
    rw [Algebra.mem_bot]
    exact ⟨⟨x.1, hxK⟩, rfl⟩
  obtain ⟨x₀, hx₀bot, hx₀sep⟩ :=
    JacobsonNoether.exists_separable_and_not_isCentral' (L := K) (D := C₀) hCproper₀
  let x : C := ⟨x₀.1, x₀.2⟩
  let fCC₀ : C →ₐ[K] C₀ :=
    { toFun := fun z ↦ ⟨z.1, z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  have hxbot : x ∉ (⊥ : Subalgebra K C) := by
    intro hx
    apply hx₀bot
    rw [Algebra.mem_bot] at hx ⊢
    rcases hx with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    ext
    exact congrArg Subtype.val ha
  have hxsep : IsSeparable K x := by
    have hinj : Function.Injective fCC₀ := fun a b hab ↦
      Subtype.ext (congrArg Subtype.val hab)
    have hfx : IsSeparable K (fCC₀ x) := by
      have hfx' : fCC₀ x = x₀ := rfl
      rw [hfx']
      exact hx₀sep
    exact (isSeparable_map_iff fCC₀ hinj).mp hfx
  exact ⟨(adjoinRootToAmbient_of_centralizer_element (k := k) (D := D) K hKfield x).range,
    adjoinRoot_range_isField_of_centralizer_element (k := k) (D := D) K hKfield x,
    adjoinRoot_range_isSeparable_of_centralizer_element
      (k := k) (D := D) K hKfield hKsep x hxsep,
    adjoinRoot_range_strict_of_nontrivial_centralizer_element
      (k := k) (D := D) K hKfield x hxbot⟩

/-- A finite central skew field over `k` contains a maximal subfield that
is separable over `k`. -/
@[stacks 0752]
theorem CSA.exists_separable_maximalSubfield :
    ∃ K : Subalgebra k D, Algebra.IsSeparable k K ∧ IsMaximalSubfield K := by
  classical
  rcases exists_finrank_maximal_separable_subfield (k := k) (D := D) with
    ⟨K, hKfield, hKsep, hmax⟩
  have hCeq : Subalgebra.centralizer k (K : Set D) = K := by
    by_contra hCK
    rcases exists_larger_separable_subfield_of_nontrivial_centralizer
      (k := k) (D := D) K hKfield hKsep hCK with
      ⟨L, hLfield, hLsep, hKL⟩
    haveI : FiniteDimensional k L :=
      FiniteDimensional.of_injective L.val.toLinearMap Subtype.val_injective
    have hfinKL : Module.finrank k K ≤ Module.finrank k L := by
      simpa using Submodule.finrank_mono (Subalgebra.toSubmodule.monotone hKL.le)
    have hfinLK : Module.finrank k L ≤ Module.finrank k K := hmax L hLfield hLsep
    have hEq : K = L := Subalgebra.eq_of_le_of_finrank_eq hKL.le (Nat.le_antisymm hfinKL hfinLK)
    exact hKL.ne hEq
  have hKmax : K.IsMaximalCommutative :=
    (K.centralizer_eq_iff_isMaximalCommutative).1 hCeq
  exact ⟨K, hKsep, { toIsMaximalCommutative := hKmax }⟩

end

namespace CSA

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)

/-- Every finite central simple `k`-algebra is split
by some finite separable extension of `k`. -/
@[stacks 0752]
theorem exists_finite_separable_splitting_field :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L),
      A.IsSplitBy L := by
  rcases exists_divisionAlgebra_brauerEquivalent k A with
    ⟨D, _, _, _, _, hAD⟩
  rcases CSA.exists_separable_maximalSubfield (k := k) (D := D) with ⟨L, hLsep, hLmax⟩
  letI : IsMaximalSubfield L := hLmax
  haveI : FiniteDimensional k L :=
    FiniteDimensional.of_injective L.val.toLinearMap Subtype.val_injective
  have hsplitD : (CSA.mk (AlgCat.of k D)).IsSplitBy L := IsMaximalSubfield.isSplitBy L
  exact ⟨L, inferInstance, inferInstance, inferInstance, hLsep,
    (A.isSplitBy_iff_of_isBrauerEquivalent L hAD).2 hsplitD⟩

end CSA

namespace BrauerGroup

variable {k : Type u} [Field k]
variable (A : Br.{u, v} k)
variable (L : Type w) [Field L] [Algebra k L]

/-- A Brauer class is split by `L` if it admits a finite central simple representative split by
`L`. -/
def IsSplitBy : Prop :=
  ∃ B : CSA.{u, max u v} k, (Quotient.mk _ B : Br(k)) = A ∧ B.IsSplitBy L

@[simp] theorem isSplitBy_mk [FiniteDimensional k L] (A : CSA.{u, max u v} k) :
    BrauerGroup.IsSplitBy (Quotient.mk _ A : Br(k)) L ↔ A.IsSplitBy L := by
  constructor
  · rintro ⟨B, hBA, hB⟩
    have hiff : A.IsSplitBy L ↔ B.IsSplitBy L := by
      exact A.isSplitBy_iff_of_isBrauerEquivalent L <| Quotient.exact hBA.symm
    exact hiff.2 hB
  · intro hA
    exact ⟨A, rfl, hA⟩

/-- Every Brauer class over `k` admits a finite separable splitting
field. -/
@[stacks 0752]
theorem exists_finite_separable_splitting_field :
    ∃ (L : Type (max u v)) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : Algebra.IsSeparable k L), A.IsSplitBy L := by
  refine Quotient.inductionOn A fun B ↦ ?_
  rcases B.exists_finite_separable_splitting_field with ⟨L, _, _, _, _, hL⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨B, rfl, hL⟩⟩

end BrauerGroup

end
