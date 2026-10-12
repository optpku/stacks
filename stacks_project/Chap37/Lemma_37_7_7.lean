/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (T : Thickening.Over X) (U : Thickening.Over Y)
  [FormallyUnramified U.left.hom]
  [IsUniversalFirstOrder T] [IsUniversalFirstOrder U]
  (f : T.left.left ⟶ U.left.left)
  (sq : IsPullback f T.left.hom U.left.hom g) [Flat g]

/- Lemma 37.7.7 (1): in a cartesian square whose lower horizontal morphism is formally
unramified and whose vertical base morphism is flat, the ambient component of the canonical
map between universal first-order thickenings is flat. -/
@[stacks 04F9] #check
  (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison_flat g T U f sq :
    Flat (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.comparison
      g T U f sq.toCommSq).right.left)

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder

namespace AlgebraicGeometry.Scheme.Hom.Conormal

variable {Z X W Y : Scheme.{u}} (h : Z ⟶ X) (h' : W ⟶ Y)
  (f : Z ⟶ W) (g : X ⟶ Y) [FormallyUnramified h']
  (sq : IsPullback f h h' g) [Flat g]

/- Lemma 37.7.7 (2): for a cartesian square with `h'` formally unramified and `g` flat, the
canonical map from the pullback of the conormal sheaf of `h'` to that of `h` is an isomorphism. -/
@[stacks 04F9] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.map_isIso_of_isPullback_of_flat_of_formallyUnramified sq :
    IsIso (AlgebraicGeometry.Scheme.Hom.Conormal.map sq.toCommSq))

end AlgebraicGeometry.Scheme.Hom.Conormal
