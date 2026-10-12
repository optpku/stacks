/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (T : Thickening.Over X) (U : Thickening.Over Y)
  [FormallyUnramified T.left.hom] [FormallyUnramified U.left.hom]
  [IsUniversalFirstOrder T] [IsUniversalFirstOrder U]
  (f : T.left.left ⟶ U.left.left) (sq : CommSq f T.left.hom U.left.hom g)

/- Lemma 37.7.5 (1): a commutative square of formally unramified morphisms canonically
extends to a morphism between their chosen universal first-order thickenings over `Y`. -/
@[stacks 04F7] #check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison g T U f sq :
    (AlgebraicGeometry.Thickening.Over.map g).obj T ⟶ U)

#check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison_left g T U f sq :
    (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison g T U f sq).left.left = f)

#check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison_comm g T U f sq :
    f ≫ U.hom.left = T.hom.left ≫
      (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison g T U f sq).right.left)

#check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison_over g T U f sq :
    (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison g T U f sq).right.left ≫
      U.right.hom = T.right.hom ≫ g)

#check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison_unique g T U f sq :
    ∀ (k : (AlgebraicGeometry.Thickening.Over.map g).obj T ⟶ U),
      k.left.left = f →
        k = AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison g T U f sq)

/- Lemma 37.7.5 (2): the square induces the canonical pullback map from the conormal sheaf of
`U.left.hom` to that of `T.left.hom`. -/
@[stacks 04F7] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.map sq :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Hom.conormalSheaf U.left.hom) ⟶
      AlgebraicGeometry.Scheme.Hom.conormalSheaf T.left.hom)

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
