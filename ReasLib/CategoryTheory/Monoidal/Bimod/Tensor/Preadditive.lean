/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.Preadditive
public import ReasLib.CategoryTheory.Monoidal.Bimod.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive balanced tensor functors of bimodules

Balanced tensor product is additive in each variable separately. This leaf records the
fixed-variable functors and their map formulas at the generic bimodule level.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [monoidalPreadditive : MonoidalPreadditive C]
variable [hasCoequalizers : HasCoequalizers C]
variable [preservesTensorLeft :
  ∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [preservesTensorRight :
  ∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {R S T : Mon C}

include monoidalPreadditive hasCoequalizers preservesTensorLeft preservesTensorRight

/-- Left whiskering of a sum of bimodule morphisms is the sum of the whiskered morphisms. -/
@[simp]
theorem whiskerLeft_add (P : Bimod R S) {Q Q' : Bimod S T} (f g : Q ⟶ Q') :
    Bimod.whiskerLeft P (f + g) = Bimod.whiskerLeft P f + Bimod.whiskerLeft P g := sorry

/-- Right whiskering of a sum of bimodule morphisms is the sum of the whiskered morphisms. -/
@[simp]
theorem whiskerRight_add {P P' : Bimod R S} (f g : P ⟶ P') (Q : Bimod S T) :
    Bimod.whiskerRight (f + g) Q = Bimod.whiskerRight f Q + Bimod.whiskerRight g Q := sorry

/-- Balanced tensor product with a fixed left bimodule is additive. -/
@[stacks 0FSA "additive generic balanced tensor functor in the right bimodule"]
instance tensorLeftAdditive (P : Bimod R S) :
    (tensorLeft (T := T) P).Additive := sorry

/-- Balanced tensor product with a fixed right bimodule is additive. -/
@[stacks 0FSA "additive generic balanced tensor functor in the left bimodule"]
instance tensorRightAdditive (Q : Bimod S T) :
    (tensorRight (R := R) Q).Additive := sorry

variable (P : Bimod R S) (Q : Bimod S T)

#synth (tensorLeft (T := T) P).Additive
#synth (tensorRight (R := R) Q).Additive

end CategoryTheory.Bimod

end
