/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GradedAlgebra.Veronese.Basic

@[expose] public section

open scoped DirectSum

universe u

namespace GradedRing.Veronese

variable {A σ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The degree-`n` summand in the Veronese direct-sum ring. -/
def grading (d n : ℕ) : Submodule ℤ (GradedRing.Veronese 𝒜 d) where
  carrier := {x | ∀ m, m ≠ n → x m = 0}
  zero_mem' := by intro m hm; rfl
  add_mem' := by
    intro x y hx hy m hm
    simp only [DirectSum.add_apply, hx m hm, hy m hm, add_zero]
  smul_mem' := by
    intro c x hx m hm
    change c • x m = 0
    rw [hx m hm, smul_zero]

/-- The additive inclusion of the Veronese direct sum in the original graded ring. -/
def inclusionAddHom (d : ℕ) : GradedRing.Veronese 𝒜 d →+ A :=
  DirectSum.toAddMonoid fun n ↦ AddSubgroupClass.subtype (𝒜 (n * d))

/-- The additive Veronese inclusion preserves the unit. -/
theorem inclusionAddHom_one (d : ℕ) : inclusionAddHom 𝒜 d 1 = 1 := sorry

/-- The additive Veronese inclusion preserves multiplication. -/
theorem inclusionAddHom_mul (d : ℕ) (x y : GradedRing.Veronese 𝒜 d) :
    inclusionAddHom 𝒜 d (x * y) = inclusionAddHom 𝒜 d x * inclusionAddHom 𝒜 d y := sorry

/-- The canonical inclusion of the Veronese ring in the original graded ring. -/
noncomputable def inclusion (d : ℕ) : GradedRing.Veronese 𝒜 d →+* A where
  toFun := inclusionAddHom 𝒜 d
  map_zero' := map_zero (inclusionAddHom 𝒜 d)
  map_add' := map_add (inclusionAddHom 𝒜 d)
  map_one' := inclusionAddHom_one 𝒜 d
  map_mul' := inclusionAddHom_mul 𝒜 d

/-- A pure Veronese element lies in its corresponding internal homogeneous component. -/
theorem of_mem_grading (d n : ℕ) (x : 𝒜 (n * d)) :
    DirectSum.of (fun k : ℕ ↦ 𝒜 (k * d)) n x ∈ grading 𝒜 d n := sorry

/-- The inclusion of one original homogeneous piece into its internal Veronese component. -/
def componentEmbedding (d n : ℕ) : 𝒜 (n * d) →+ grading 𝒜 d n where
  toFun x := ⟨DirectSum.of (fun k : ℕ ↦ 𝒜 (k * d)) n x, of_mem_grading 𝒜 d n x⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (DirectSum.of (fun k : ℕ ↦ 𝒜 (k * d)) n)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (DirectSum.of (fun k : ℕ ↦ 𝒜 (k * d)) n) x y

/-- Coordinate embedding and summation are inverse for the internal Veronese grading. -/
theorem decomposition_laws (d : ℕ) :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (grading 𝒜 d))
      (DirectSum.toAddMonoid fun n ↦
        (DirectSum.of (fun i : ℕ ↦ grading 𝒜 d i) n).comp (componentEmbedding 𝒜 d n)) ∧
    Function.RightInverse (DirectSum.coeAddMonoidHom (grading 𝒜 d))
      (DirectSum.toAddMonoid fun n ↦
        (DirectSum.of (fun i : ℕ ↦ grading 𝒜 d i) n).comp (componentEmbedding 𝒜 d n)) := sorry

/-- The explicit coordinate decomposition of the Veronese ring into its internal summands. -/
@[implicit_reducible]
noncomputable def decomposition (d : ℕ) : DirectSum.Decomposition (grading 𝒜 d) where
  decompose' := DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (fun i : ℕ ↦ grading 𝒜 d i) n).comp (componentEmbedding 𝒜 d n)
  left_inv := (decomposition_laws 𝒜 d).1
  right_inv := (decomposition_laws 𝒜 d).2

/-- The coordinate grading contains the unit in degree zero and respects multiplication. -/
theorem grading_laws (d : ℕ) :
    (1 : GradedRing.Veronese 𝒜 d) ∈ grading 𝒜 d 0 ∧
    (∀ {i j : ℕ} {x y : GradedRing.Veronese 𝒜 d},
      x ∈ grading 𝒜 d i → y ∈ grading 𝒜 d j → x * y ∈ grading 𝒜 d (i + j)) := sorry

/-- The coordinate summands give the Veronese ring its canonical internal grading. -/
noncomputable instance instGradedRingGrading (d : ℕ) : GradedRing (grading 𝒜 d) where
  one_mem := (grading_laws 𝒜 d).1
  mul_mem := fun {i j} {x y} hx hy ↦ (grading_laws 𝒜 d).2 hx hy
  decompose' := (decomposition 𝒜 d).decompose'
  left_inv := (decomposition 𝒜 d).left_inv
  right_inv := (decomposition 𝒜 d).right_inv

/-- Evaluation at degree `n` on an internally homogeneous Veronese element. -/
noncomputable def componentValue (d n : ℕ) : grading 𝒜 d n →+ 𝒜 (n * d) :=
  (DirectSum.component ℤ ℕ (fun k : ℕ ↦ (𝒜 (k * d) : Type u)) n).toAddMonoidHom.comp
    (grading 𝒜 d n).subtype

/-- The inclusion of an internally homogeneous Veronese element is its unique nonzero
coordinate. -/
theorem inclusion_eq_componentValue (d n : ℕ) (x : grading 𝒜 d n) :
    inclusion 𝒜 d x = componentValue 𝒜 d n x := sorry

/-- The canonical Veronese inclusion sends the internal degree `n` piece into degree `n * d`. -/
theorem inclusion_mem (d : ℕ) {n : ℕ} {x : GradedRing.Veronese 𝒜 d}
    (hx : x ∈ grading 𝒜 d n) : inclusion 𝒜 d x ∈ 𝒜 (n * d) := by
  rw [inclusion_eq_componentValue 𝒜 d n ⟨x, hx⟩]
  exact (componentValue 𝒜 d n ⟨x, hx⟩).property

/-- Multiplying a degree-`n` numerator by the `(d - 1)`st power of a degree-`n`
denominator produces degree `n * d`. -/
theorem numerator_mem (d n : ℕ) (hd : 1 ≤ d) (a b : 𝒜 n) :
    (a : A) * (b : A) ^ (d - 1) ∈ 𝒜 (n * d) := sorry

/-- The `d`th power of a degree-`n` denominator has degree `n * d`. -/
theorem denominator_mem (d n : ℕ) (b : 𝒜 n) :
    (b : A) ^ d ∈ 𝒜 (n * d) := sorry

/-- The Veronese numerator representing the same degree-zero fraction as `a / b`. -/
noncomputable def fractionNumerator (d n : ℕ) (hd : 1 ≤ d) (a b : 𝒜 n) : grading 𝒜 d n :=
  componentEmbedding 𝒜 d n
    ⟨(a : A) * (b : A) ^ (d - 1), numerator_mem 𝒜 d n hd a b⟩

/-- The Veronese denominator representing the same degree-zero fraction as `a / b`. -/
noncomputable def fractionDenominator (d n : ℕ) (b : 𝒜 n) : grading 𝒜 d n :=
  componentEmbedding 𝒜 d n ⟨(b : A) ^ d, denominator_mem 𝒜 d n b⟩

end GradedRing.Veronese
