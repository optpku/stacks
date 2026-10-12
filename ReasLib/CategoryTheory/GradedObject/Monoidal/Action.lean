/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Actions on graded objects

Homogeneous left-action maps assemble into a morphism from the convolution tensor product.  The
construction is independent of algebras, complexes, and sheaves, and complements the right-action
assembler used for graded monoid modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory.GradedObject.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {I : Type w} [AddMonoid I]

/-- Assemble homogeneous left-action maps into a morphism from the graded tensor product. -/
@[stacks 0FRS "homogeneous left-action assembler"]
noncomputable def leftActionHom (A M : GradedObject I C) [HasTensor A M]
    (act : ∀ i j : I, A i ⊗ M j ⟶ M (i + j)) : tensorObj A M ⟶ M :=
  fun _ ↦ tensorObjDesc (X₁ := A) (X₂ := M) fun i j h ↦
    act i j ≫ eqToHom (congrArg M h)

/-- Restricting an assembled graded left action to a homogeneous summand recovers the supplied
action map followed by the requested degree identification. -/
@[reassoc]
theorem ι_leftActionHom (A M : GradedObject I C) [HasTensor A M]
    (act : ∀ i j : I, A i ⊗ M j ⟶ M (i + j)) (i j n : I) (h : i + j = n) :
    ιTensorObj A M i j n h ≫ leftActionHom A M act n =
      act i j ≫ eqToHom (congrArg M h) := sorry

/-- On a summand in its canonical total degree, an assembled graded left action is the original
homogeneous action map. -/
@[reassoc (attr := simp)]
theorem ι_leftActionHom_add (A M : GradedObject I C) [HasTensor A M]
    (act : ∀ i j : I, A i ⊗ M j ⟶ M (i + j)) (i j : I) :
    ιTensorObj A M i j (i + j) rfl ≫ leftActionHom A M act (i + j) = act i j := sorry

/-- Morphisms of graded objects commute with assembled left actions when they preserve every
homogeneous action map. -/
theorem leftActionHom_naturality {A B M N : GradedObject I C}
    [HasTensor A M] [HasTensor B N]
    (actM : ∀ i j : I, A i ⊗ M j ⟶ M (i + j))
    (actN : ∀ i j : I, B i ⊗ N j ⟶ N (i + j)) (f : A ⟶ B) (g : M ⟶ N)
    (h : ∀ i j : I, actM i j ≫ g (i + j) = (f i ⊗ₘ g j) ≫ actN i j) :
    leftActionHom A M actM ≫ g = tensorHom f g ≫ leftActionHom B N actN := sorry

end CategoryTheory.GradedObject.Monoidal

end
