module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace SmallToBig

/- 59.99.1.1: (f_big,* F)|S_etale = f_small,* (F|T_etale).
Restriction of the big étale direct image agrees with the small étale direct image
of the restriction. The displayed equality is realized by a canonical isomorphism
between the chosen sheaf presentations. -/
@[stacks 0759] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.bigToSmallPushforwardIso :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type (u + 1))]
    (F : Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1))),
    (siteMorphismOfTopoi S).pushforward.obj
        ((Big.morphismOfTopoi f).pushforward.obj F) ≅
      (smallMorphism f).pushforward.obj
        ((siteMorphismOfTopoi T).pushforward.obj F))

end SmallToBig
end AlgebraicGeometry.Scheme.Etale

end
