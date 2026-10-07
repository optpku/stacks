module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u

/- Lemma 33.9.4 (Tag 0FD1): if `X` is proper over the field `k`, then the canonical morphism
`X ⟶ Spec(Γ(X, ⊤))` has geometrically connected fibers. -/
@[stacks 0FD1] #check
  (AlgebraicGeometry.geometricallyConnected_toSpecΓ_of_isProper :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
      geometrically (ConnectedSpace ·) X.toSpecΓ)
