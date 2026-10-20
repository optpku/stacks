/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import ReasLib.AlgebraicGeometry.FormalScheme.FunctorOfPoints

/-!
# Sheaf conditions for formal-scheme functors of points

The functor of points of a formal scheme satisfies fpqc and fppf descent.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.FormalScheme

/-- The unrestricted functor of points of a formal scheme `X`, sending a scheme
`S` to morphisms `toFormalScheme.obj S ⟶ X`, is a sheaf for
`Scheme.fpqcTopology`. -/
theorem isSheaf_fpqc (X : FormalScheme.{u}) :
    Presheaf.IsSheaf Scheme.fpqcTopology
      (Scheme.toFormalScheme.op ⋙ yoneda.obj X) :=
  sorry

/-- The functor of points of a formal scheme, restricted to a small bound-closed
full subcategory of schemes, is a sheaf for the restricted fpqc topology. -/
theorem functorOfPoints_isSheaf_fpqc {P : ObjectProperty Scheme.{u}}
    (hP : Scheme.IsSmallBoundClosed P) (X : FormalScheme.{u}) :
    Presheaf.IsSheaf (P.ι.restrictedTopology Scheme.fpqcTopology)
      ((functorOfPoints P).obj X) :=
  sorry

/-- The unrestricted functor of points of a formal scheme `X` is a sheaf for
`Scheme.fppfTopology`. -/
theorem isSheaf_fppf (X : FormalScheme.{u}) :
    Presheaf.IsSheaf Scheme.fppfTopology
      (Scheme.toFormalScheme.op ⋙ yoneda.obj X) :=
  sorry

end AlgebraicGeometry.FormalScheme
