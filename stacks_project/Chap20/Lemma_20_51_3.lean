/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.InternalHom
import StacksCheckRecall

@[expose] public section

/- Lemma 20.51.3 (1): derived pullback preserves internal Hom out of a perfect object. -/
@[stacks 0GM7 "(1)"]
#check @AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom.isIso_of_isPerfect

/- Lemma 20.51.3 (2): flat derived pullback preserves internal Hom from a pseudo-coherent object
into a locally bounded-below object. -/
@[stacks 0GM7 "(2)"]
#check @AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom.isIso_of_isFlat

/- Lemma 20.51.3 (3): the same comparison is invertible for a finite-Tor-dimension morphism. -/
@[stacks 0GM7 "(3)"]
#check @AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom.isIso_of_finiteTorDimension

#check @AlgebraicGeometry.RingedSpace.modulePullbackDerived.InternalHom.comparison
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyBoundedBelow
#check @RingedSpace.Hom.HasFiniteTorDimension
