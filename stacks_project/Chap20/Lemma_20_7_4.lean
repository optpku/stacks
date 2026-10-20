/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.Restriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Restriction

/- Lemma 20.7.4 (1): higher direct image commutes with restriction to an open subspace. -/
@[stacks 01E5 "restriction of a higher direct image to an open"]
#check @object_isomorphic

/- Lemma 20.7.4 (2): the analogous restriction statement for bounded-below derived
pushforward. -/
@[stacks 01E5 "bounded-below derived pushforward commutes with open restriction"]
#check @boundedBelow_isomorphic

-- The unbounded functor-level comparison is the reusable companion behind both statements.
#check @derived_isomorphic
