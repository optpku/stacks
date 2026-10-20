/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

universe u

/- Lemma 75.8.2: Derived pushforward preserves bounded-below coherent cohomology
when the cohomology sheaves have support proper over the base scheme. -/
@[stacks 0D0R] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pushforwardDerived_boundedBelowCoherent_of_properSupport :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (f : X ⟶ Y) [LocallyOfFiniteType f] [IsNoetherian Y]
      (E : ModuleDerived X),
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X)) E →
      (t.plus : ObjectProperty (ModuleDerived X)) E →
      (∀ i : ℤ, ClosedSubset.ProperOver (SchemeRealization.toBase X)
        (Modules.closedSupport
          ((DerivedCategory.homologyFunctor (Modules X) i).obj E))) →
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent (structureSheaf Y))
          ((Modules.moduleDerivedPushforward f).obj E) ∧
        (t.plus : ObjectProperty (ModuleDerived Y))
          ((Modules.moduleDerivedPushforward f).obj E))
