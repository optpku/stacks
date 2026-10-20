module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.FppfPushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open scoped MorphismOfTopoiIn

noncomputable section

universe u

/- Lemma 59.100.3 -/
@[stacks 0DDN] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.proper_fppfSmallPushforward_isIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology (Type (u + 1))]
      [HasSheafify Y.smallEtaleTopology (Type (u + 1))]
      [IsProper f],
      IsIso
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.fppfSmallPushforwardHom f))

end

end
