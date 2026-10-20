/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Smooth

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Smooth

/-- If a composite of scheme morphisms is smooth and the second factor is étale, then the
first factor is smooth. -/
theorem of_comp {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.Smooth (f ≫ g)] [AlgebraicGeometry.Etale g] :
    AlgebraicGeometry.Smooth f := sorry

end AlgebraicGeometry.Smooth
