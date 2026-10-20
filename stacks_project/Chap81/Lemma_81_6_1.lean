module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.Thickening
import StacksCheckRecall

/-!
# Lemma 81.6.1

A scheme-theoretic pushout of a thickening and an affine morphism of schemes over `S`
remains a pushout in algebraic spaces over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 81.6.1 -/
@[stacks 07SY]
#check (AlgebraicGeometry.AlgebraicSpace.isPushout_ofOver_thickening_affine :
    ∀ {S : Scheme.{u}} {X X' Y Y' : Over S},
      (i : X ⟶ X') → (f : X ⟶ Y) → (i' : X' ⟶ Y') → (g : Y ⟶ Y') →
      [AlgebraicGeometry.IsThickening i.left] → [IsAffineHom f.left] →
      IsPushout i.left f.left i'.left g.left →
      IsPushout ((schemeFunctor S).map i) ((schemeFunctor S).map f)
        ((schemeFunctor S).map i') ((schemeFunctor S).map g))

end AlgebraicGeometry.AlgebraicSpace
