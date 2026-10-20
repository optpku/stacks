module

import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Sheaf
import StacksCheckRecall

open CategoryTheory

universe u v w

variable (X : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : X.carrier)
  (F : (Over S)ᵒᵖ ⥤ Type w)

/- Lemma 38.34.17 (1): a presheaf on the chosen big h-site slice is an h sheaf
exactly when it is a Zariski sheaf and satisfies descent for every proper,
surjective morphism of finite presentation. -/
@[stacks 0EU5] #check
  (AlgebraicGeometry.ChosenBigHSite.Sheaf.iffZariskiAndEqualizer X S F :
    Presheaf.IsSheaf (AlgebraicGeometry.ChosenBigHSite.bigTopology X S) F ↔
      Presheaf.IsSheaf
          (AlgebraicGeometry.ChosenBigHSite.bigZariskiTopology X S) F ∧
        AlgebraicGeometry.ChosenBigHSite.Equalizer.IsProperSurjective X S F)

/- Lemma 38.34.17 (2): assuming the Zariski sheaf condition, the preceding
descent property may be tested on morphisms with affine represented target. -/
@[stacks 0EU5] #check
  (AlgebraicGeometry.ChosenBigHSite.Equalizer.iffAffine X S F :
      Presheaf.IsSheaf
          (AlgebraicGeometry.ChosenBigHSite.bigZariskiTopology X S) F →
      (AlgebraicGeometry.ChosenBigHSite.Equalizer.IsProperSurjective X S F ↔
        AlgebraicGeometry.ChosenBigHSite.Equalizer.IsAffineProperSurjective X S F))
