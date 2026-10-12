/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Grothendieck
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

noncomputable section

/- Theorem 19.11.7: every Grothendieck abelian category admits functorial injective embeddings. -/
@[stacks 079H] #check
  fun (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] ↦
    (inferInstance : HasFunctorialInjectives C)

end

end CategoryTheory
