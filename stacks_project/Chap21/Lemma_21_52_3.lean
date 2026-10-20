/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Compact.LocalizedGenerator
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.52.3

The reusable statement is relative compactness of the canonical degree-zero localized generator.
`IsCompactObjectOn t.plus` tests coproducts in the ambient derived category and requires their
apex to be bounded below, exactly matching the source formulation of compactness in `D⁺`.
-/

/- Lemma 21.52.3 (0G21): if every cohomology functor over `U` commutes with coproducts, then
`j_!𝒪_U[0]` is compact on ambient derived coproducts whose apex is bounded below. -/
@[stacks 0G21]
#check @RingedSite.Hom.ModuleDerived.LocalizedGenerator.isCompactOnBoundedBelow

#check @RingedSite.Hom.ModuleDerived.localizedGenerator
#check @RingedSite.Hom.ModuleCohomology.PreservesCoproducts
#check @CategoryTheory.IsCompactObjectOn.preservesColimit
#check @CategoryTheory.Limits.Sigma.summandRetract
#check @CategoryTheory.DerivedCategory.IsGE.exists_injective_model
