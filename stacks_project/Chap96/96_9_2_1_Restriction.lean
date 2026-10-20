/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Restriction

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u a b

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {A : Type a} [Category.{b} A] (x : X.total) (F : X.totalᵒᵖ ⥤ A)

#check (AlgebraicGeometry.GroupoidsOver.smallEtaleEval x :
    (X.p.obj x).left.Etale ⥤ X.total)

#check (AlgebraicGeometry.GroupoidsOver.restrictSmallEtale x F :
    (X.p.obj x).left.Etaleᵒᵖ ⥤ A)
