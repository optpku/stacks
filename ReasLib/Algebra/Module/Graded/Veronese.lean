/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GradedAlgebra.Veronese.Internal
public import ReasLib.Algebra.Group.Action.NatInt
public import Mathlib.Algebra.Module.GradedModule

/-!
# Veronese modules

Selected homogeneous pieces form a direct sum with the restricted Veronese-ring action and
its coordinate-supported internal grading.
-/

@[expose] public section

open scoped DirectSum

universe u

namespace GradedModule

variable {A σ M τ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable [AddCommGroup M] [Module A M] [SetLike τ M] [AddSubgroupClass τ M]
variable (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

/-- The `d`th Veronese module is the direct sum of the pieces whose degrees are multiples of
`d`. -/
abbrev Veronese (d : ℕ) :=
  ⨁ n : ℤ, ℳ (n * (d : ℤ))

namespace Veronese

/-- The degree calculation for the action of a Veronese ring piece on a Veronese module piece. -/
theorem smulDegree (d i : ℕ) (j : ℤ) :
    i * d +ᵥ j * (d : ℤ) = (i +ᵥ j) * (d : ℤ) := by
  change ((i * d : ℕ) : ℤ) + j * (d : ℤ) = ((i : ℤ) + j) * (d : ℤ)
  rw [Nat.cast_mul, add_mul]

/-- Homogeneous scalar multiplication restricts to the pieces selected by the Veronese
indices, with its target degree transported by the multiplication identity. -/
def smul (d : ℕ) {i : ℕ} {j : ℤ}
    (x : GradedRing.Veronese.degree 𝒜 d i) (y : ℳ (j * (d : ℤ))) :
    ℳ ((i +ᵥ j) * (d : ℤ)) :=
  Eq.mp (congrArg (fun n : ℤ ↦ (ℳ n : Type u)) (smulDegree d i j))
    (⟨(x : A) • (y : M), SetLike.GradedSMul.smul_mem x.2 y.2⟩ :
      ℳ (i * d +ᵥ j * (d : ℤ)))

/-- The restricted homogeneous action is unital, associative, and additive in both variables. -/
theorem gradedModule_laws (d : ℕ) :
    (∀ b : GradedMonoid (fun n : ℤ ↦ ℳ (n * (d : ℤ))),
      GradedMonoid.mk (A := fun n : ℤ ↦ ℳ (n * (d : ℤ))) _ (smul 𝒜 ℳ d (GradedRing.Veronese.one 𝒜 d) b.snd) = b) ∧
    (∀ (a a' : GradedMonoid (GradedRing.Veronese.degree 𝒜 d))
        (b : GradedMonoid (fun n : ℤ ↦ ℳ (n * (d : ℤ)))),
      GradedMonoid.mk (A := fun n : ℤ ↦ ℳ (n * (d : ℤ))) _ (smul 𝒜 ℳ d (a * a').snd b.snd) =
        GradedMonoid.mk (A := fun n : ℤ ↦ ℳ (n * (d : ℤ))) _ (smul 𝒜 ℳ d a.snd (smul 𝒜 ℳ d a'.snd b.snd))) ∧
    (∀ {i : ℕ} {j : ℤ} (a : GradedRing.Veronese.degree 𝒜 d i)
        (b c : ℳ (j * (d : ℤ))),
      smul 𝒜 ℳ d a (b + c) = smul 𝒜 ℳ d a b + smul 𝒜 ℳ d a c) ∧
    (∀ {i : ℕ} {j : ℤ} (a : GradedRing.Veronese.degree 𝒜 d i),
      smul 𝒜 ℳ d a (0 : ℳ (j * (d : ℤ))) = 0) ∧
    (∀ {i : ℕ} {j : ℤ} (a a' : GradedRing.Veronese.degree 𝒜 d i)
        (b : ℳ (j * (d : ℤ))),
      smul 𝒜 ℳ d (a + a') b = smul 𝒜 ℳ d a b + smul 𝒜 ℳ d a' b) ∧
    (∀ {i : ℕ} {j : ℤ} (b : ℳ (j * (d : ℤ))),
      smul 𝒜 ℳ d (0 : GradedRing.Veronese.degree 𝒜 d i) b = 0) := sorry

/-- The selected pieces form an explicit external graded module for the restricted action. -/
@[implicit_reducible]
noncomputable def gradedModule (d : ℕ) :
    DirectSum.Gmodule (GradedRing.Veronese.degree 𝒜 d)
      (fun n : ℤ ↦ ℳ (n * (d : ℤ))) where
  smul := smul 𝒜 ℳ d
  one_smul := (gradedModule_laws 𝒜 ℳ d).1
  mul_smul := (gradedModule_laws 𝒜 ℳ d).2.1
  smul_add := fun {i j} a b c ↦ (gradedModule_laws 𝒜 ℳ d).2.2.1 a b c
  smul_zero := fun {i j} a ↦ (gradedModule_laws 𝒜 ℳ d).2.2.2.1 a
  add_smul := fun {i j} a b c ↦ (gradedModule_laws 𝒜 ℳ d).2.2.2.2.1 a b c
  zero_smul := fun {i j} b ↦ (gradedModule_laws 𝒜 ℳ d).2.2.2.2.2 b

/-- The external graded-module instance exposes the fixed restricted homogeneous action. -/
noncomputable instance instGmodule (d : ℕ) :
    DirectSum.Gmodule (GradedRing.Veronese.degree 𝒜 d)
      (fun n : ℤ ↦ ℳ (n * (d : ℤ))) := gradedModule 𝒜 ℳ d

/-- The selected direct sum is canonically a module over the Veronese ring. -/
noncomputable instance instModule (d : ℕ) :
    Module (GradedRing.Veronese 𝒜 d) (GradedModule.Veronese ℳ d) :=
  DirectSum.Gmodule.module (GradedRing.Veronese.degree 𝒜 d)
    (fun n : ℤ ↦ ℳ (n * (d : ℤ)))

/-- The internal degree-`n` subgroup of a Veronese module. -/
def grading (d : ℕ) (n : ℤ) : Submodule ℤ (GradedModule.Veronese ℳ d) where
  carrier := {x | ∀ m, m ≠ n → x m = 0}
  zero_mem' := by intro m hm; rfl
  add_mem' := by
    intro x y hx hy m hm
    simp only [DirectSum.add_apply, hx m hm, hy m hm, add_zero]
  smul_mem' := by
    intro c x hx m hm
    change c • x m = 0
    rw [hx m hm, smul_zero]

/-- A pure selected module element lies in its corresponding internal Veronese component. -/
theorem of_mem_grading (d : ℕ) (n : ℤ) (x : ℳ (n * (d : ℤ))) :
    DirectSum.of (fun k : ℤ ↦ ℳ (k * (d : ℤ))) n x ∈ grading ℳ d n := sorry

/-- The inclusion of a selected homogeneous piece into its internal Veronese-module degree. -/
def componentEmbedding (d : ℕ) (n : ℤ) : ℳ (n * (d : ℤ)) →+ grading ℳ d n where
  toFun x := ⟨DirectSum.of (fun k : ℤ ↦ ℳ (k * (d : ℤ))) n x, of_mem_grading ℳ d n x⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (DirectSum.of (fun k : ℤ ↦ ℳ (k * (d : ℤ))) n)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (DirectSum.of (fun k : ℤ ↦ ℳ (k * (d : ℤ))) n) x y

/-- Coordinate embedding and summation are inverse for the internal Veronese-module grading. -/
theorem decomposition_laws (d : ℕ) :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (grading ℳ d))
      (DirectSum.toAddMonoid fun n ↦
        (DirectSum.of (fun i : ℤ ↦ grading ℳ d i) n).comp (componentEmbedding ℳ d n)) ∧
    Function.RightInverse (DirectSum.coeAddMonoidHom (grading ℳ d))
      (DirectSum.toAddMonoid fun n ↦
        (DirectSum.of (fun i : ℤ ↦ grading ℳ d i) n).comp (componentEmbedding ℳ d n)) := sorry

/-- The explicit coordinate decomposition of the Veronese module into its internal summands. -/
@[implicit_reducible]
noncomputable def decomposition (d : ℕ) : DirectSum.Decomposition (grading ℳ d) where
  decompose' := DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (fun i : ℤ ↦ grading ℳ d i) n).comp (componentEmbedding ℳ d n)
  left_inv := (decomposition_laws ℳ d).1
  right_inv := (decomposition_laws ℳ d).2

/-- The internal decomposition instance exposes the fixed coordinate decomposition. -/
noncomputable instance instDecomposition (d : ℕ) :
    DirectSum.Decomposition (grading ℳ d) := decomposition ℳ d

/-- The internal Veronese grading is preserved by the canonical Veronese-ring action. -/
noncomputable instance instGradedSMul (d : ℕ) :
    SetLike.GradedSMul (GradedRing.Veronese.grading 𝒜 d) (grading ℳ d) where
  smul_mem := sorry


end Veronese

end GradedModule
