/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.Linear
public import ReasLib.CategoryTheory.Monoidal.Bimod.Tensor.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear balanced tensor functors of bimodules

In a monoidal `k`-linear category, balanced tensor product is `k`-linear in each variable
separately. The product-domain bifunctor is deliberately not declared jointly linear.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe w u v

namespace CategoryTheory.Bimod

variable {k : Type w} [Semiring k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear k C]
variable [MonoidalCategory C] [monoidalPreadditive : MonoidalPreadditive C]
variable [monoidalLinear : MonoidalLinear k C]
variable [hasCoequalizers : HasCoequalizers C]
variable [preservesTensorLeft :
  ∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [preservesTensorRight :
  ∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {R S T : Mon C}

include monoidalPreadditive monoidalLinear hasCoequalizers preservesTensorLeft preservesTensorRight

/-- Left whiskering of a scalar multiple is the scalar multiple of the whiskered morphism. -/
@[simp]
theorem whiskerLeft_smul (r : k) (P : Bimod R S) {Q Q' : Bimod S T} (f : Q ⟶ Q') :
    Bimod.whiskerLeft P (r • f) = r • Bimod.whiskerLeft P f := sorry

/-- Right whiskering of a scalar multiple is the scalar multiple of the whiskered morphism. -/
@[simp]
theorem whiskerRight_smul (r : k) {P P' : Bimod R S} (f : P ⟶ P') (Q : Bimod S T) :
    Bimod.whiskerRight (r • f) Q = r • Bimod.whiskerRight f Q := sorry

/-- Balanced tensor product with a fixed left bimodule is `k`-linear. -/
@[stacks 0FSA "linear generic balanced tensor functor in the right bimodule"]
instance tensorLeftLinear (P : Bimod R S) :
    Functor.Linear k (tensorLeft (T := T) P) := sorry

/-- Balanced tensor product with a fixed right bimodule is `k`-linear. -/
@[stacks 0FSA "linear generic balanced tensor functor in the left bimodule"]
instance tensorRightLinear (Q : Bimod S T) :
    Functor.Linear k (tensorRight (R := R) Q) := sorry

variable (P : Bimod R S) (Q : Bimod S T)

#synth Functor.Linear k (tensorLeft (T := T) P)
#synth Functor.Linear k (tensorRight (R := R) Q)

end CategoryTheory.Bimod

end
