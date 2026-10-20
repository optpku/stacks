/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GeometricallyReduced

/-!
# The object property of geometrically reduced families of curves

`𝒞urves^{geomred}` is the full subcategory of families of curves whose fibres
are geometrically reduced in the sense of Definition 76.29.2. Membership is the
source-facing packaging of a classifying morphism factoring through that open
substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReduced :
    ∀ (S : Scheme.{u}), ObjectProperty (Obj S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReduced_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      geometricallyReduced S P ↔
        ∀ y : Points (ofOver (base P)), y ∈ geometricallyReducedFiberLocus (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_geometricallyReduced :
    ∀ (S : Scheme.{u}), (geometricallyReduced S).IsClosedUnderIsomorphisms)

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
