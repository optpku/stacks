/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Monoidal
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProductCompatibility
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.33.3

Commutativity of the relative derived cup product is the braiding law of the canonical lax
braided derived pushforward.
-/

/- Lemma 21.33.3 (0FPM): the relative derived cup product commutes with the braidings on the
source and target derived categories. -/
@[stacks 0FPM]
#check @CategoryTheory.relativeDerivedCupProduct_commutative_commSq

#check @RingedSite.Hom.modulePushforwardDerived.cupProduct
#check @RingedSite.Hom.modulePushforwardDerived.laxBraided
