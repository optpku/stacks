module

public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Adjunction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped Bicategory

universe u v w

namespace CategoryTheory.FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, w} C}
variable (F : X ⟶ Y)

/- Lemma 4.33.14: every `1`-morphism `F : X ⟶ Y` of fibred categories over `C` factors as
`F = u ≫ v`, where `u` is fully faithful, `w` is left adjoint to `u`, and `v` is fibred. -/
@[stacks 08NF]
#check (CategoryTheory.FiberedCategoryOver.AdjointFactorization.exists F :
  ∃ X' : FiberedCategoryOver C, ∃ u : X ⟶ X', ∃ v : X' ⟶ Y, ∃ w : X' ⟶ X,
    ∃ h_u : (toFunctor u).FullyFaithful, ∃ h_adj : w ⊣ u,
      ∃ h_v : (toFunctor v).IsFibered, F = u ≫ v)

end CategoryTheory.FiberedCategoryOver
