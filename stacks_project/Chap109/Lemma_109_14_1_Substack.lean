/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.IsolatedSingularities

/-! # The isolated-singularities condition on families of curves -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.isolatedSingularities :
  (S : Scheme.{u}) → CategoryTheory.ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.isolatedSingularities_iff :
  ∀ {S : Scheme.{u}} (P : Obj S),
    isolatedSingularities S P ↔ IsolatedSingularities (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.inverseImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    OpenSubspace X → (Y ⟶ X) → OpenSubspace Y)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.mkOfSchemeOverField :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
    topologicalKrullDim X.left ≤ 1 → Obj (Spec (CommRingCat.of k)))

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
