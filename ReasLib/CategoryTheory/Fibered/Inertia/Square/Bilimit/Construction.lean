module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Basic
public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Comparison.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bilimit construction for the relative-inertia square

This module owns the canonical pseudo-pullback cone and its bilimit instance.
Projection readouts for the cone live in `Bilimit.Computations`.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory
namespace BasedCategory

open BasedNatIso BasedNatTrans
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X Y : BasedCategory.{max v vB, max w (max u (max v vB))} C}

namespace RelativeInertia

namespace Square

/-- Canonical relative-inertia pseudo-pullback square of a based functor.

Its legs are `toTarget F`, `RelativeInertia.toInertia F`, `Inertia.identitySection Y`, and
`Inertia.map F`; the comparison identifies the two composites into `inertia Y`. -/
@[stacks 04Z6 "relative-inertia pseudo-pullback cone"]
def cone (F : X ⥤ᵇ Y) :
    Bicategory.PseudoPullbackCone
      (B := BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (Inertia.identitySection Y) (Inertia.map F) where
  pt := relativeInertia F
  fst := toTarget F
  snd := RelativeInertia.toInertia F
  iso := comparisonIso F

/-- Lemma 4.34.3 (Stacks 04Z6): the relative-inertia square is a bilimit in the homogeneous
universe of the ambient bicategory of based categories. -/
@[stacks 04Z6 "relative-inertia square is a categorical pullback and bilimit witness"]
instance cone.isBilimit (F : X ⥤ᵇ Y) :
    (cone F).IsBilimit := sorry
/- Proof strategy: a competing cone supplies an inertia object in `X` whose image in `Y` is
isomorphic to a neutral automorphism. Lift this to relative inertia; naturality supplies the
factorization cells, and `RelativeInertia.hom_ext` gives uniqueness. -/

end Square

end RelativeInertia

end BasedCategory
end CategoryTheory
