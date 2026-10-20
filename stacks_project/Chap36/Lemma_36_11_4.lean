/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Coherent

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Lemma 36.11.4: bounded-below derived pushforward along a locally finite type morphism to a
Noetherian scheme has coherent cohomology when every cohomology sheaf has proper support over
the base. -/
@[stacks 0D0B] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforwardBoundedBelowCoherentOfProperSupport :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]
      (E : DerivedCategory.Plus.CohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf))
      [∀ i : ℤ, Modules.HasProperSupportOver f
        ((DerivedCategory.Plus.homologyFunctor X.toRingedSpace.Modules i).obj E.obj)],
      DerivedCategory.Plus.cohomologyIn
        (SheafOfModules.isCoherent S.toRingedSpace.ringCatSheaf)
        ((RingedSpace.moduleDerivedPushforwardPlus f.toShHom).obj E.obj))

end AlgebraicGeometry.Scheme.ModuleDerived
