module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Stack
import StacksCheckRecall

/-!
# Lemma 95.16.1

The functor `p : Pic_{X/B} ⟶ (Sch/S)_fppf` is a stack in groupoids, up to the
small-fiber replacement of Remark 8.4.9.

The fibers are essentially `u`-small, rather than merely small in the larger
ambient universe. This is the fiberwise size condition for the replacement
in Remark 8.4.9.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 95.16.1: up to a replacement as in Remark 8.4.9, the functor
`p : Pic_{X/B} ⟶ (Sch/S)_fppf` sending `(U, b, L)` to `U` is a stack in groupoids
over `(Sch/S)_fppf`. -/
@[stacks 04WN] #check (AlgebraicGeometry.AlgebraicSpace.Picard.isStackInGroupoids :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    IsStack.InGroupoids (Scheme.fppfTopology.over S)
      (AlgebraicGeometry.AlgebraicSpace.Picard.p f))

/- The fiberwise essential-smallness condition used in Remark 8.4.9. -/
#check (AlgebraicGeometry.AlgebraicSpace.Picard.fibers_essentiallySmall :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (U : Over S),
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((AlgebraicGeometry.AlgebraicSpace.Picard.p f).Fiber U)))
