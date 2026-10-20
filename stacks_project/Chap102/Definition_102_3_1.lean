/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped Bicategory

universe u

/- Definition 102.3.1: a 1-morphism f : 𝒳 ⟶ 𝒴 of categories fibred in groupoids
over (Sch/S)_fppf is limit preserving if for every directed inverse limit
U = lim U_i of affine schemes over S, the square of fibre categories
colim 𝒳_{U_i} ⟶ 𝒳_U over colim 𝒴_{U_i} ⟶ 𝒴_U is 2-cartesian. -/
@[stacks 0CMR] #check (AlgebraicGeometry.Groupoids.Hom.LimitPreserving :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S},
    (X ⟶ Y) → Prop)
