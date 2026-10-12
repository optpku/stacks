/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Duality.Biproduct
import StacksCheckRecall

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
variable [MonoidalPreadditive C] [HasBinaryBiproducts C]
variable {X₁ Y₁ X₂ Y₂ : C}

/- Lemma 12.17.2: binary biproducts of explicit left-dual pairings are paired componentwise.
The shared theorem is stated under the minimal binary-biproduct assumption. -/
@[stacks 0FFT] #check
  (ExactPairing.biprod :
    ExactPairing X₁ Y₁ → ExactPairing X₂ Y₂ →
      ExactPairing (X₁ ⊞ X₂) (Y₁ ⊞ Y₂))

/- The chosen-left-dual form is available as a coherent reusable instance. -/
#check HasLeftDual.biprod

end CategoryTheory
