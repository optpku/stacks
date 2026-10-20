module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.Differentials.Conormal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.11.12: let `T.left.hom : T.left.left ⟶ X` represent a formally
unramified morphism by a universal first-order thickening `T`. If
`T.left.hom ≫ f : T.left.left ⟶ S` is formally smooth, then the canonical
conormal-differentials complex is short exact. -/
@[stacks 06B7] #check
  (AlgebraicGeometry.FormallySmooth.conormalDifferentials_shortExact :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}}
      (T : AlgebraicGeometry.Thickening.Over X) (f : X ⟶ S)
      [AlgebraicGeometry.FormallyUnramified T.left.hom]
      [AlgebraicGeometry.Thickening.IsUniversalFirstOrder T]
      [AlgebraicGeometry.FormallySmooth (T.left.hom ≫ f)],
      (AlgebraicGeometry.Thickening.IsUniversalFirstOrder.Differentials.complex T f).ShortExact)
