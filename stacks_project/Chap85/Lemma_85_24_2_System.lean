/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocallyGiven.Simplicial

/-!
# Compatible simplicial restrictions of locally given derived modules

The compatible-restriction data and their canonical comparisons are re-exported
from the derived-module library.
-/

@[expose] public section

open CategoryTheory RingedSite

universe u v w uB vB

#check (RingedSite.ModuleDerived.LocallyGiven.negativeSelfExt :
  ∀ {X : RingedSite.{u, v, w}} {B : Type uB} [Category.{vB} B],
    (h_le : UnivLE.{max u v, w}) →
    @RingedSite.ModuleDerived.LocallyGiven.{u, v, w, w, uB, vB} h_le X B inferInstance → Prop)
