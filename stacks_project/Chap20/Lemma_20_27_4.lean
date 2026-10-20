/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.27.4 (08DE): `L(f)^*` is the total left derived functor of pullback on module
sheaves.  The reusable owner infers the canonical homology and additive structures. -/
@[stacks 08DE "Lemma 20.27.4: derived pullback universal property"]
#check @modulePullbackDerived.isLeftDerivedFunctor

@[stacks 08DE "derived pullback source functor"]
#check @modulePullbackToDerived
@[stacks 08DE "derived pullback functor"]
#check @modulePullbackDerived

end AlgebraicGeometry.RingedSpace
