module

public import stacks_project.Chap45.Proposition_45_12_1_Theory
public import stacks_project.Chap45.Proposition_45_12_1_TotalChernClass
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass

/- Proposition 45.12.1
There is a unique total Chern class on the Grothendieck groups of finite locally free modules,
with multiplicativity, normalization, grading, pullback naturality, and the line-bundle formula. -/
@[stacks 0FI5] #check
  (AlgebraicGeometry.ChernClass.existsUniqueTotalChernClass :
    ∀ {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
      (A : Cᵒᵖ ⥤ RingCat.{x})
      (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
      [∀ X, GradedAlgebra (Agrade X)]
      (S : AlgebraicGeometry.ChernClass.Theory toScheme A Agrade),
      ∃ c : AlgebraicGeometry.ChernClass.TotalChernClass
          toScheme A Agrade S.firstChernClass,
        ∀ c', c' = c)

end AlgebraicGeometry.ChernClass
