module

public import stacks_project.Chap84.«84_5_2_1_Comparison»
public import stacks_project.Chap84.«84_5_2_1_Site»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

noncomputable section

universe u

/- 84.5.2.1: (f_big,* F)|_{X_étale} = f_small,* (F|_{Y_étale}).
Restriction of the big étale direct image of a sheaf on `(Spaces/Y)_étale`
agrees with the small étale direct image of the restricted sheaf. If `F` is
an `𝒪`-module on the big ringed site, the identification is an isomorphism
of `𝒪_X`-modules on `X_étale`. The displayed equality is realized by a
canonical isomorphism between the chosen sheaf presentations. -/
@[stacks 0DG9] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.bigToSmallPushforwardIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
      (F : Sheaf (overEtaleTopology Y) (Type (u + 1))),
      (restrictToSmallEtale X).obj ((bigPushforward f).obj F) ≅
        (sheafPushforwardType f).obj ((restrictToSmallEtale Y).obj F))

end
