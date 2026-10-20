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
open DerivedCategory.TStructure

noncomputable section

universe u

/- Lemma 36.11.3: derived pushforward along a locally finite type morphism to a
Noetherian scheme preserves bounded coherent cohomology when every cohomology sheaf
has proper support over the base. -/
@[stacks 08E2] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforwardBoundedCoherentOfProperSupport :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType f]
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
      (hE_coherent : DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E)
      (hE_bounded : (t.bounded : ObjectProperty
        (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)) E)
      [∀ i : ℤ, AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f
        (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf E i)],
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent S.toRingedSpace.ringCatSheaf)
          ((AlgebraicGeometry.RingedSpace.moduleDerivedPushforward f.toShHom).obj E) ∧
        (t.bounded : ObjectProperty
          (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace))
          ((AlgebraicGeometry.RingedSpace.moduleDerivedPushforward f.toShHom).obj E))
