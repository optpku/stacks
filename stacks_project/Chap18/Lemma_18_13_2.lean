module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
import StacksCheckRecall

/-!
# Lemma 18.13.2

The module pullback-pushforward adjunction is owned by
`ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  (f : X.Hom Y)
variable [f.modulePushforward.{z}.IsRightAdjoint]
variable (G : ModuleCat.{z} Y) (F : ModuleCat.{z} X)

/- Lemma 18.13.2 (03D7): the canonical Hom equivalence expressing
`f.modulePullback ⊣ f.modulePushforward`. -/
@[stacks 03D7]
#check
  (modulePullbackHomEquiv.{z} f G F :
    (f.modulePullback.{z}.obj G ⟶ F) ≃ (G ⟶ f.modulePushforward.{z}.obj F))

end RingedSite.Hom
