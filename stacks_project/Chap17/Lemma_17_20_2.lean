/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
import StacksCheckRecall

/-!
# Lemma 17.20.2

Exactness of pullback along a flat morphism is owned for arbitrary ringed spaces in ReasLib.
-/

@[expose] public section

/- Lemma 17.20.2: pullback along a flat morphism of ringed spaces is exact. -/
@[stacks 02N4]
#check @RingedSpace.Hom.IsFlat.pullback_exact

/- The finite-limit half of exactness is available directly to categorical downstream code. -/
#check @RingedSpace.Hom.pullback_preservesFiniteLimits_of_isFlat

/- Stalkwise construction and categorical stability are part of the shared flatness API. -/
#check @RingedSpace.Hom.IsFlat.atPoint
#check @RingedSpace.Hom.IsFlat.of_forall_flatAt
#check @RingedSpace.Hom.IsFlat.id
#check @RingedSpace.Hom.IsFlat.comp
