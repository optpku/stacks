/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u a b

variable {S : Scheme.{u}} {X : GroupoidsOver S}

namespace AlgebraicGeometry.GroupoidsOver

/-- The selected small-étale evaluation arrow is strongly cartesian over its
displayed base arrow. -/
instance smallEtaleEval_toBase.isStronglyCartesian (x : X.total)
    (V' : (X.p.obj x).left.Etale) :
    X.p.IsStronglyCartesian (etaleOver x V').hom (smallEtaleEval_toBase x V') :=
  CategoryTheory.Functor.Chosen.cartesianHom.isStronglyCartesian
    X.p (etaleOver x V').hom ⟨x, rfl⟩

end AlgebraicGeometry.GroupoidsOver

variable {A : Type a} [Category.{b} A] {x y : X.total} (φ : x ⟶ y)
variable (F : X.totalᵒᵖ ⥤ A) (V' : (X.p.obj y).left.Etale)

#check (AlgebraicGeometry.GroupoidsOver.comparisonPushHom φ V' :
    (GroupoidsOver.smallEtaleEval x).obj
        ((Scheme.smallEtalePullback (X.p.map φ).left).obj V') ⟶
      (GroupoidsOver.smallEtaleEval y).obj V')

#check (AlgebraicGeometry.GroupoidsOver.comparisonPush φ F :
    GroupoidsOver.restrictSmallEtale y F ⟶
      (Scheme.smallEtalePullback (X.p.map φ).left).op ⋙
        GroupoidsOver.restrictSmallEtale x F)
