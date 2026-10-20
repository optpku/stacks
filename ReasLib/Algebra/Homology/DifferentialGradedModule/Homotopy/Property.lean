/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy

/-!
# Homotopy Equivalences of Differential Graded Modules

This file exposes homotopy equivalences as a morphism property on ordinary differential graded
modules.  The definition is pulled back from the canonical property on closed degree-zero maps,
so downstream diagram APIs can use it without unpacking representatives in the homotopy category.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory DifferentialGradedCategory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- A DG-module map is a homotopy equivalence when it becomes invertible in the differential
graded homotopy category. -/
@[stacks 09JX "homotopy equivalences of differential graded modules"]
abbrev homotopyEquivalences (A : CochainDGAlgebra.{u, v} R) :
    MorphismProperty (DifferentialGradedModule.{u, w} A) :=
  (MorphismProperty.isomorphisms (DifferentialGradedCategory.K R
    (DifferentialGradedModule.{u, w} A))).inverseImage (toK A)

/-- Membership in `homotopyEquivalences` is equivalently invertibility after applying `toK`. -/
theorem homotopyEquivalences_iff
    {A : CochainDGAlgebra.{u, v} R}
    {K L : DifferentialGradedModule.{u, w} A} (f : K ⟶ L) :
    homotopyEquivalences A f ↔ IsIso ((toK A).map f) := sorry

/-- A concrete homotopy equivalence witness makes its forward map a homotopy equivalence. -/
theorem homotopyEquivalences_of_exists_inverse
    {A : CochainDGAlgebra.{u, v} R}
    {K L : DifferentialGradedModule.{u, w} A} (f : K ⟶ L)
    (h : ∃ g : L ⟶ K, Nonempty (Homotopy (f ≫ g) (𝟙 K)) ∧
      Nonempty (Homotopy (g ≫ f) (𝟙 L))) :
    homotopyEquivalences A f := sorry

variable (A : CochainDGAlgebra.{u, v} R)

end DifferentialGradedModule
