/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Exact.DivisionRing
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

section

variable {k : Type u} {V : Type v} {W : Type w} {X : Type z}
variable [DivisionRing k] [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
variable [Module k V] [Module k W] [Module k X]

/- Lemma 9.4.2: the source field statement is the field specialization of the reusable
division-ring splitting theorem. -/
@[stacks 09FP]
#check (Function.Exact.existsLinearEquivProdOfDivisionRing :
  ∀ {f : V →ₗ[k] W} {g : W →ₗ[k] X}, Function.Exact f g → Function.Injective f →
    Function.Surjective g →
      ∃ e : W ≃ₗ[k] V × X,
        f = e.symm ∘ₗ LinearMap.inl k V X ∧ g = LinearMap.snd k V X ∘ₗ e)

end
