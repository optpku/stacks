/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.RationalMap.ComponentStalk
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.49.2: for schemes `X` and `Y` over `S`, with `X` having finitely many
irreducible components, component-stalk evaluation of `S`-rational maps is injective when
`Y ⟶ S` is locally of finite type. -/
@[stacks 0BX8] #check
  (@AlgebraicGeometry.Scheme.RationalMap.componentStalkMap_injective_of_locallyOfFiniteType :
    ∀ {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
      [Finite (irreducibleComponents X)] [LocallyOfFiniteType (Y ↘ S)],
      Function.Injective
        (AlgebraicGeometry.Scheme.RationalMap.componentStalkMap S X Y))

/- The component-stalk evaluation map is bijective when `Y ⟶ S` is locally of finite
presentation. -/
#check
  (@AlgebraicGeometry.Scheme.RationalMap.componentStalkMap_bijective_of_locallyOfFinitePresentation :
    ∀ {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
      [Finite (irreducibleComponents X)] [LocallyOfFinitePresentation (Y ↘ S)],
      Function.Bijective
        (AlgebraicGeometry.Scheme.RationalMap.componentStalkMap S X Y))

/- The component-stalk evaluation map is bijective when `Y ⟶ S` is locally of finite type
and `X` is reduced. -/
#check
  (@AlgebraicGeometry.Scheme.RationalMap.componentStalkMap_bijective_of_locallyOfFiniteType_of_isReduced :
    ∀ {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
      [Finite (irreducibleComponents X)] [LocallyOfFiniteType (Y ↘ S)] [IsReduced X],
      Function.Bijective
        (AlgebraicGeometry.Scheme.RationalMap.componentStalkMap S X Y))
