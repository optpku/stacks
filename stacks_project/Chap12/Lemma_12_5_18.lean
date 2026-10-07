module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import StacksCheckRecall

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Lemma 12.5.18 (1): the six-term snake construction is functorial in snake inputs, so
the complete induced kernel-cokernel diagram commutes. -/
@[stacks 08N7] #check
  (ShortComplex.SnakeInput.composableArrowsFunctor :
    ShortComplex.SnakeInput C ⥤ ComposableArrows C 5)

variable {S₁ S₂ : ShortComplex.SnakeInput C} (f : S₁ ⟶ S₂)

/- Lemma 12.5.18 (2): in particular, the central square containing the connecting
morphisms commutes. -/
#check
  (ShortComplex.SnakeInput.naturality_δ f :
    S₁.δ ≫ f.f₃.τ₁ = f.f₀.τ₃ ≫ S₂.δ)

end CategoryTheory
