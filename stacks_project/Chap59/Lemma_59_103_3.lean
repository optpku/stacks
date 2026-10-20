module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

universe u

/- Lemma 59.103.3: for a proper morphism of schemes, the canonical small étale to big h
pushforward comparison is an isomorphism on sheaves of sets. -/
@[stacks 0EWA] #check
  (AlgebraicGeometry.Scheme.HComparison.proper_smallHPushforward_isIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology (Type (u + 1))]
      [HasSheafify Y.smallEtaleTopology (Type (u + 1))] [IsProper f],
      IsIso (AlgebraicGeometry.Scheme.HComparison.smallHPushforwardHom f))

end
