/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.Locus

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

open AlgebraicGeometry

/- The Gorenstein locus and its pointwise membership characterization. -/
#check
  (AlgebraicGeometry.Scheme.Hom.gorensteinLocus :
    ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → Set X)

#check
  (AlgebraicGeometry.Scheme.Hom.mem_gorensteinLocus :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
      x ∈ f.gorensteinLocus ↔ f.gorensteinAt x)

end AlgebraicGeometry.Scheme.Hom
