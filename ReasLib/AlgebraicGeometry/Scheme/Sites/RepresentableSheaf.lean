/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A presheaf on the fppf site over a scheme is a sheaf if it admits a relatively
representable natural transformation to a sheaf. -/
theorem isSheaf_fppfTopology_over_of_relativelyRepresentable
    {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : yoneda.relativelyRepresentable a)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F := sorry

end AlgebraicGeometry
