module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.Integral
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.54.8: An integral birational morphism between integral schemes with normal target is
an isomorphism. -/
@[stacks 0AB1] #check
  (AlgebraicGeometry.IsBirational.isIso_of_isIntegralHom_of_isNormal :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
      [IsBirational f] [IsIntegralHom f], Y.isNormal → IsIso f)
