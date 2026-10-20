/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

/- Lemma 20.48.4: if `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` is a morphism of ringed
spaces and `E` is an object of `D(𝒪_Y)` with tor-amplitude in `[a, b]`, then the derived
pullback `L(f)^* E` has tor-amplitude in `[a, b]`.  The reusable owner has only the
mathematical inputs `(f, E, [a, b])`; module-category instances are canonical. -/
@[stacks 09U8]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Pullback.hasTorAmplitudeIn

#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Pullback.hasFiniteTorDimension
