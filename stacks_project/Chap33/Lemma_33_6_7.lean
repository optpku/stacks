/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.Product
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory

/- Lemma 33.6.7 (1): if `X` is geometrically reduced at `x` and `Y` is reduced,
then every point of `X ×ₖ Y` above `x` has reduced local ring. -/
@[stacks 035Z] #check
  (AlgebraicGeometry.SchemeOverField.isReduced_stalk_pullback_of_geometricallyReducedAt_of_isReduced :
    ∀ {k : Type u} [Field k]
      (X Y : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (x : X.left) (hX : AlgebraicGeometry.SchemeOverField.geometricallyReducedAt X x)
      [AlgebraicGeometry.IsReduced Y.left],
      ∀ z : (CategoryTheory.Limits.pullback X.hom Y.hom : AlgebraicGeometry.Scheme),
        CategoryTheory.Limits.pullback.fst X.hom Y.hom z = x →
          _root_.IsReduced
            ((CategoryTheory.Limits.pullback X.hom Y.hom : AlgebraicGeometry.Scheme).presheaf.stalk z))

/- Lemma 33.6.7 (2): if `X` is geometrically reduced over `k` and `Y` is
reduced, then `X ×ₖ Y` is reduced. -/
@[stacks 035Z] #check
  (AlgebraicGeometry.SchemeOverField.isReduced_pullback_of_geometricallyReduced_of_isReduced :
    ∀ {k : Type u} [Field k]
      (X Y : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (hX : AlgebraicGeometry.SchemeOverField.geometricallyReduced X)
      [AlgebraicGeometry.IsReduced Y.left],
      AlgebraicGeometry.IsReduced
        (CategoryTheory.Limits.pullback X.hom Y.hom : AlgebraicGeometry.Scheme))

/- Lemma 33.6.7 (3): if `X` and `Y` are geometrically reduced over `k`, then
`X ×ₖ Y` is geometrically reduced over `k`. -/
@[stacks 035Z] #check
  (AlgebraicGeometry.SchemeOverField.geometricallyReduced_pullback_of_geometricallyReduced :
    ∀ {k : Type u} [Field k]
      (X Y : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (hX : AlgebraicGeometry.SchemeOverField.geometricallyReduced X)
      (hY : AlgebraicGeometry.SchemeOverField.geometricallyReduced Y),
      AlgebraicGeometry.SchemeOverField.geometricallyReduced
        (CategoryTheory.Over.mk
          (CategoryTheory.Limits.pullback.fst X.hom Y.hom ≫ X.hom) :
            CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))))

/- Lemma 33.6.7 (4): over a perfect field, the fiber product of two reduced
schemes is reduced. -/
@[stacks 035Z] #check
  (AlgebraicGeometry.SchemeOverField.isReduced_pullback_of_isReduced_of_perfectField :
    ∀ {k : Type u} [Field k] [PerfectField k]
      (X Y : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
      [AlgebraicGeometry.IsReduced X.left] [AlgebraicGeometry.IsReduced Y.left],
      AlgebraicGeometry.IsReduced
        (CategoryTheory.Limits.pullback X.hom Y.hom : AlgebraicGeometry.Scheme))
