/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.ChernCharacter
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass

/- Proposition 45.12.4: if every cohomology ring `A(X)` is a `ℚ`-algebra,
there is a unique natural ring-valued Chern character on `K₀(Vect(X))` whose
value on a line-bundle class `L` is `exp(c₁(L))`. -/
@[stacks 0FI9] #check
  (AlgebraicGeometry.ChernClass.existsUniqueChernCharacter :
    ∀ {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
      (A : Cᵒᵖ ⥤ RingCat.{x})
      (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
      [∀ X, GradedAlgebra (Agrade X)] [∀ X, Algebra ℚ (A.obj (Opposite.op X))]
      (S : AlgebraicGeometry.ChernClass.Theory toScheme A Agrade),
      ∃ ch : AlgebraicGeometry.ChernClass.ChernCharacter
          toScheme A Agrade S.firstChernClass,
        ∀ ch', ch' = ch)

end AlgebraicGeometry.ChernClass
