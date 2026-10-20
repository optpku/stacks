module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Diagonal
import StacksCheckRecall

/-!
# Cancellation of representability by algebraic spaces along postcomposition

If the relative diagonal of `b : G ⟶ H` and the composite `a ≫ b` are
representable by algebraic spaces, then so is `a`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.3.10: let `S` be a scheme. For maps `a : F ⟶ G` and `b : G ⟶ H` of
presheaves on `(Sch/S)_fppf`, if the relative diagonal
`pullback.diagonal b : G ⟶ pullback b b` (Stacks `Δ : G ⟶ G ×_H G`) and the
composite `a ≫ b` (Stacks `b ∘ a`) are representable by algebraic spaces, then
so is `a`. -/
@[stacks 0AMN]
#check (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.of_comp :
  ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H)
    [HasPullback b b],
    representableByAlgebraicSpaces (pullback.diagonal b) →
    representableByAlgebraicSpaces (a ≫ b) → representableByAlgebraicSpaces a)

end AlgebraicGeometry.AlgebraicSpace
