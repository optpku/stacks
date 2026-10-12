/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials.Transitivity
import StacksCheckRecall

/-!
# Lemma 29.34.16

For composable scheme morphisms `X ⟶ Y ⟶ S`, smoothness of `X ⟶ Y` makes the transitivity
sequence of relative differentials short exact.

@stack 02K4
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

/- Lemma 29.34.16: For composable scheme morphisms `f : X ⟶ Y` and `g : Y ⟶ S`,
if `f` is smooth, then the canonical relative-differentials transitivity complex is
short exact. -/
@[stacks 02K4] #check
  (AlgebraicGeometry.Smooth.relativeDifferentialsTransitivity_shortExact :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ S) [AlgebraicGeometry.Smooth f],
      (AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity.complex
        f.toShHom g.toShHom).ShortExact)
