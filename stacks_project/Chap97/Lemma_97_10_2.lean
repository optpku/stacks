/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

universe u

/- Lemma 97.10.2: for morphisms `Z ⟶ B`, `X ⟶ B`, and `B' ⟶ B` of algebraic spaces
over a scheme `S`, with `Z' = B' ×_B Z` and `X' = B' ×_B X`, the fppf sheaves on
`Sch/S` satisfy `Mor_{B'}(Z', X') ≅ B' ×_B Mor_B(Z, X)`. -/
@[stacks 05Y4]
#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.pullbackIso :
    ∀ {S : Scheme.{u}} {B B' : AlgebraicSpace S} (Z X : Over B) (h : B' ⟶ B),
      sheaf (pullbackObj Z h).hom (pullbackObj X h).hom ≅
        pullback (toSheaf.map h) (baseMap Z X))
