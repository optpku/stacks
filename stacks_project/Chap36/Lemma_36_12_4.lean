/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Descent

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

/- Lemma 36.12.4: for an fpqc covering family `family` of a scheme `X`, a derived
`𝒪_X`-module `E` is perfect if and only if every derived pullback along a member of
`family` is perfect. -/
@[stacks 09UG] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPerfect_iff_fpqcCovering :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (family : ι → Over X) (hfamily : AlgebraicGeometry.Scheme.FpqcCovering family)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect E ↔
        ∀ i : ι, AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
          ((AlgebraicGeometry.RingedSpace.modulePullbackDerived
            (family i).hom.toLRSHom.toShHom).obj E))
