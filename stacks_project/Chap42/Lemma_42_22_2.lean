/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 42.22.2: if `X` is locally of finite type over `S` and
`f : Y ⟶ X` and `g : Z ⟶ Y` are envelopes, then `g ≫ f` is an envelope. -/
@[stacks 0GU6] #check (AlgebraicGeometry.IsEnvelope.comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.IsEnvelope f] [AlgebraicGeometry.IsEnvelope g],
    AlgebraicGeometry.IsEnvelope (f ≫ g))
