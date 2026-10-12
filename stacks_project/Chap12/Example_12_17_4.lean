/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.GradedObject.KoszulBraiding
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory MonoidalCategory

variable {F : Type u} [Field F]

/- Example 12.17.4: graded vector spaces carry the explicit Koszul symmetric structure.  It is
kept as a value because the unsigned pointwise braiding is a second coherent choice. -/
@[stacks 0FFX] #check
  (koszulSymmetricCategory : SymmetricCategory (GradedObject ℤ (ModuleCat F)))

/- On homogeneous tensors the shared braiding is the signed ordinary swap. -/
#check (ι_koszulBraiding_hom :
  ∀ (V W : GradedObject ℤ (ModuleCat F)) (p q n : ℤ) (h : p + q = n),
    ιTensorObj V W p q n h ≫ (koszulBraiding V W).hom n =
      koszulBraidingComponent V W p q ≫
        ιTensorObj W V q p n (Eq.trans (add_comm q p) h))

end CategoryTheory.GradedObject.Monoidal
