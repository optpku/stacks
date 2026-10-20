/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Differentials

/-!
# Conormal sequence of an immersion of algebraic spaces

The canonical conormal complex is exact and its differential comparison is an
epimorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {B X Z : AlgebraicSpace S}
variable (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ B)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials.exact_and_epi i f :
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials.complex i f).Exact ∧
    Epi (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials.comparison i f))
