/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GradedAlgebra.Veronese.Basic
public import ReasLib.Algebra.Group.Action.NatInt
public import Mathlib.Algebra.Module.GradedModule

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
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

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

/-- The inclusion of one original homogeneous piece into the matching internal Veronese
component. -/
def componentEmbedding (d n : ℕ) : 𝒜 (n * d) →+ grading 𝒜 d n where
  toFun x := ⟨DirectSum.of (fun k : ℕ ↦ 𝒜 (k * d)) n x, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- The explicit coordinate decomposition of the Veronese direct-sum ring into its summands. -/
@[implicit_reducible]
noncomputable def decomposition (d : ℕ) : DirectSum.Decomposition (grading 𝒜 d) where
  decompose' := DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (fun i : ℕ ↦ grading 𝒜 d i) n).comp
      (componentEmbedding 𝒜 d n)
  left_inv := sorry
  right_inv := sorry

/-- The coordinate summands give the Veronese direct-sum ring its canonical internal grading. -/
noncomputable instance instGradedRingGrading (d : ℕ) : GradedRing (grading 𝒜 d) where
  one_mem := sorry
  mul_mem := sorry
  decompose' := (decomposition 𝒜 d).decompose'
  left_inv := (decomposition 𝒜 d).left_inv
  right_inv := (decomposition 𝒜 d).right_inv

/-- A pure Veronese element lies in its corresponding internal homogeneous component. -/
theorem of_mem_grading (d n : ℕ) (x : 𝒜 (n * d)) :
    DirectSum.of (fun k : ℕ ↦ 𝒜 (k * d)) n x ∈ grading 𝒜 d n := sorry

/-- Evaluation at degree `n` on an internally homogeneous Veronese element. -/
noncomputable def componentValue (d n : ℕ) : grading 𝒜 d n →+ 𝒜 (n * d) :=
  (DirectSum.component ℤ ℕ (fun k : ℕ ↦ (𝒜 (k * d) : Type u)) n).toAddMonoidHom.comp
    (grading 𝒜 d n).subtype

/-- The inclusion of an internally homogeneous Veronese element is its unique nonzero
coordinate. -/
theorem inclusion_eq_componentValue (d n : ℕ) (x : grading 𝒜 d n) :
    inclusion 𝒜 d x = componentValue 𝒜 d n x := sorry

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
    i * d +ᵥ j * (d : ℤ) = (i +ᵥ j) * (d : ℤ) := sorry

/-- The original graded action restricts to an external graded action on the selected pieces. -/
noncomputable instance instGmodule (d : ℕ) :
    DirectSum.Gmodule (GradedRing.Veronese.degree 𝒜 d)
      (fun n : ℤ ↦ ℳ (n * (d : ℤ))) where
  smul := fun {i j} x y ↦
    Eq.mp (congrArg (fun n : ℤ ↦ (ℳ n : Type u)) (smulDegree d i j))
      (⟨(x : A) • (y : M), SetLike.GradedSMul.smul_mem x.2 y.2⟩ :
        ℳ (i * d +ᵥ j * (d : ℤ)))
  one_smul := sorry
  mul_smul := sorry
  smul_add := sorry
  smul_zero := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The selected direct sum is canonically a module over the Veronese ring. -/
noncomputable instance instModule (d : ℕ) :
    Module (GradedRing.Veronese 𝒜 d) (GradedModule.Veronese ℳ d) :=
  DirectSum.Gmodule.module (GradedRing.Veronese.degree 𝒜 d)
    (fun n : ℤ ↦ ℳ (n * (d : ℤ)))

/-- The internal degree-`n` subgroup of a Veronese module. -/
def grading (d : ℕ) (n : ℤ) : Submodule ℤ (GradedModule.Veronese ℳ d) where
  carrier := {x | ∀ m, m ≠ n → x m = 0}
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- The inclusion of a selected original homogeneous piece into its Veronese-module degree. -/
def componentEmbedding (d : ℕ) (n : ℤ) :
    ℳ (n * (d : ℤ)) →+ grading ℳ d n where
  toFun x := ⟨DirectSum.of (fun k : ℤ ↦ ℳ (k * (d : ℤ))) n x, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- The coordinate decomposition of the Veronese module into its internal homogeneous pieces. -/
@[implicit_reducible]
noncomputable instance instDecomposition (d : ℕ) :
    DirectSum.Decomposition (grading ℳ d) where
  decompose' := DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (fun i : ℤ ↦ grading ℳ d i) n).comp
      (componentEmbedding ℳ d n)
  left_inv := sorry
  right_inv := sorry

/-- The internal Veronese grading is preserved by the canonical Veronese-ring action. -/
noncomputable instance instGradedSMul (d : ℕ) :
    SetLike.GradedSMul (GradedRing.Veronese.grading 𝒜 d) (grading ℳ d) where
  smul_mem := sorry

/-- A pure selected module element lies in its corresponding internal Veronese component. -/
theorem of_mem_grading (d : ℕ) (n : ℤ) (x : ℳ (n * (d : ℤ))) :
    DirectSum.of (fun k : ℤ ↦ ℳ (k * (d : ℤ))) n x ∈ grading ℳ d n := sorry

end Veronese

end GradedModule
