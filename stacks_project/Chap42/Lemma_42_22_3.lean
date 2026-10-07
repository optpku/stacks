module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 42.22.3: if `X` and `X'` are locally of finite type over a universally
catenary scheme `S` with dimension function `δ`, then the base change of an envelope
`f : Y ⟶ X.left` along an `S`-morphism `g : X' ⟶ X` is again an envelope. -/
@[stacks 0GU7]
#check (AlgebraicGeometry.IsEnvelope.pullback_of_locallyOfFiniteType :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X X' : Over S)
    [AlgebraicGeometry.LocallyOfFiniteType X.hom]
    [AlgebraicGeometry.LocallyOfFiniteType X'.hom]
    (g : X' ⟶ X) {Y : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X.left) [AlgebraicGeometry.IsEnvelope f],
    AlgebraicGeometry.IsEnvelope (Limits.pullback.snd f g.left))
