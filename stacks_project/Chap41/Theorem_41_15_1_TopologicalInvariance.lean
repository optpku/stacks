/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Thickening

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

#check
  (overPullbackMap_bijective_of_isThickening :
    ∀ {S₀ S : Scheme.{u}} (i : S₀ ⟶ S) [IsThickening i]
      (X Y : Over S) [Etale X.hom],
      Function.Bijective (fun f : Y ⟶ X ↦ (Over.pullback i).map f))

end AlgebraicGeometry.Etale
