/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
import StacksCheckRecall

@[expose] public section

/- Lemma 21.19.1 (07A6): the canonical total-derived module pullback and pushforward form an
adjunction.  Its `Adjunction.homEquiv` is the bifunctorial Hom identification in the source. -/
@[stacks 07A6]
#check @RingedSite.Hom.moduleDerivedAdjunction

#check @RingedSite.Hom.DerivedAdjunction.HasPair
#check @CategoryTheory.Adjunction.homEquiv
