module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig.Comparison

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

variable {X : ChosenBigProetaleSite.{u, v}} {S T : X.carrier} (f : T ⟶ S)
variable [UnivLE.{max u v, w}] [HasWeakSheafify (smallTopology X T) (Type w)]

/- Lemma 61.12.16: small-site base change induces the small geometric morphism. -/
@[stacks 098T] #check (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.smallMorphism.{u, v, w} f :
  MorphismOfTopoiIn.{max u v, max u v, u, u, w} (smallTopology X S) (smallTopology X T))

#check (AlgebraicGeometry.ChosenBigProetaleSite.SmallToBig.smallPullback_comp_relocalization_id_iso f :
  smallPullback f ⋙ SmallToBig.relocalizationFunctor (𝟙 T) ≅
    SmallToBig.relocalizationFunctor (𝟙 S) ⋙ Big.pullback f)

end AlgebraicGeometry.ChosenBigProetaleSite
