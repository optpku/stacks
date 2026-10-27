/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Associated
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module

/-!
# Restriction of quasi-coherent modules to small étale sites
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace QCoh

/-- Restriction of a quasi-coherent module along an object `x` of `X` to the
small étale site of `p(x)`. -/
def restrictToSmallEtale (X : GroupoidsOver S) (x : X.total) :
    QCoh X ⥤ RingedSite.ModuleCat.{u}
      (Scheme.Etale.Small.ringedSite (X.p.obj x).left) :=
  toEtaleModules X ⋙ restrictModulesToSmallEtale X x

/-- `restrictToSmallEtale` is étale transport followed by small-étale
restriction. -/
theorem restrictToSmallEtale_eq (X : GroupoidsOver S) (x : X.total) :
    restrictToSmallEtale X x =
      toEtaleModules X ⋙ restrictModulesToSmallEtale X x := sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
