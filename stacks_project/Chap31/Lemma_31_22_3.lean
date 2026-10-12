/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion.FlatAt
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 31.22.3: a relative quasi-regular immersion `i : Z ⟶ X` over `f : X ⟶ S`
forces `f` to be flat at the image of every `x : Z` whose local ring in `X` is Noetherian. -/
@[stacks 063T] #check
  (@AlgebraicGeometry.RelativeQuasiRegularImmersion.flatAt :
    ∀ {X S Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
      [AlgebraicGeometry.RelativeQuasiRegularImmersion f i] (x : Z)
      [IsNoetherianRing (X.presheaf.stalk (i.base x))],
      AlgebraicGeometry.Scheme.Hom.flatAt f (i.base x))
