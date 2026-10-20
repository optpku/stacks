module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Construction

/-!
# Strict involutivity of the pseudo-pullback swap

Swapping twice restores the original explicit pseudo-pullback based functor.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open scoped Bicategory BasedFunctor

universe u v uX vX uY vY uS vS

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {S : BasedCategory.{vS, uS} C}

namespace PseudoPullback

noncomputable section

/-- Swapping twice is the identity based functor. -/
theorem swap.involution.eqId (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S) :
    swap F G ⋙ swap G F = 𝟙 (PseudoPullback F G) := sorry
/- Proof strategy: ext first on objects and then with `hom_ext`. Swapping twice restores the two
components, while taking the inverse of the stored comparison twice returns the original iso. -/

end

end PseudoPullback
end BasedCategory
end CategoryTheory
