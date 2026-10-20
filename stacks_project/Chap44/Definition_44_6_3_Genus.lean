/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus

@[expose] public section

open AlgebraicGeometry

universe u

#check
  (AlgebraicGeometry.Curve.genus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
      [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom], ℕ)

#check
  (AlgebraicGeometry.Curve.genus_def :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
      [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom],
      AlgebraicGeometry.Curve.genus X =
        Scheme.Hom.cohomologyFinrank X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)
