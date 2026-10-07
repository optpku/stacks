module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Thickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.3.2: an invertible module on the ambient source of a morphism of
thickenings is relatively ample exactly when its restriction to the closed source is. -/
@[stacks 0D2R] #check
  (AlgebraicGeometry.Thickening.Hom.relativelyAmple_iff :
    ∀ {T U : AlgebraicGeometry.Thickening.{u}} (g : T ⟶ U) (L' : T.right.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L'],
      AlgebraicGeometry.RelativelyAmple g.right L' ↔
        AlgebraicGeometry.RelativelyAmple g.left
          ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj L'))
