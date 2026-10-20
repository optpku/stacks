/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pullback

/-! Compatibility checks for the promoted small pro-étale pullback API. -/

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 61.12.19 - small pro-étale pullback compatibility. -/
#check (AlgebraicGeometry.Scheme.smallProetalePullback :
  ∀ {S T : Scheme.{u}}, (T ⟶ S) → S.ProEt ⥤ T.ProEt)

#check (AlgebraicGeometry.Scheme.smallProetalePullback_isContinuous :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    Functor.IsContinuous (AlgebraicGeometry.Scheme.smallProetalePullback f)
      (AlgebraicGeometry.Scheme.ProEt.topology S)
      (AlgebraicGeometry.Scheme.ProEt.topology T))
