/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Functor.Spanning
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

universe vC uC vD uD

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasZeroObject C] [HasZeroObject D]
variable [Preadditive C] [Preadditive D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [∀ i : ℤ, (shiftFunctor C i).Additive]
variable [∀ i : ℤ, (shiftFunctor D i).Additive]
variable [Pretriangulated C] [Pretriangulated D]

/- Lemma 57.11.1: an exact functor with both adjoints is fully faithful when a set of objects
detects zero objects from both Hom directions and shifted Homs between those objects are
preserved bijectively. -/
@[stacks 0G24] #check
  (CategoryTheory.Functor.fullyFaithful_of_spanning :
    ∀ (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
      [F.IsLeftAdjoint] [F.IsRightAdjoint] (S : Set C)
      (h_right_orthogonal : ∀ K : C,
        (∀ (E : C), E ∈ S → ∀ (i : ℤ) (f : E ⟶ K⟦i⟧), f = 0) → IsZero K)
      (h_left_orthogonal : ∀ K : C,
        (∀ (E : C), E ∈ S → ∀ (i : ℤ) (f : K ⟶ E⟦i⟧), f = 0) → IsZero K)
      (h_shiftedHom : ∀ (E E' : C), E ∈ S → E' ∈ S → ∀ i : ℤ,
        Function.Bijective (fun f : E ⟶ E'⟦i⟧ ↦ ShiftedHom.map f F)),
      Nonempty F.FullyFaithful)

end CategoryTheory.Functor
