/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.19.6

The commutative counit square is the canonical factorization law for a total-derived adjunction;
the ringed-site adjunction is its direct specialization.
-/

/- Lemma 21.19.6 (0FPI): the comparison maps from underived to derived pullback and pushforward
intertwine the underived counit with the counit of the total-derived adjunction. -/
@[stacks 0FPI]
#check @CategoryTheory.Adjunction.TotalDerived.HasPair.derived_counit_fac_app

#check @RingedSite.Hom.moduleDerivedAdjunction
#check @RingedSite.Hom.DerivedAdjunction.HasPair
#check @CategoryTheory.Adjunction.derivedε_fac_app
