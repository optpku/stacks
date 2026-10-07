module

public import stacks_project.Chap95.«95_7_0_1_Spaces»
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Lemma 95.7.2

The functor `p : Spaces ⥤ (Sch/S)_fppf` satisfies conditions (1) and (2)
of Stacks Definition 8.4.1: it is fibered, and Hom-presheaves of fiber
objects are sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Lemma 95.7.2: the functor `p : Spaces ⥤ (Sch/S)_fppf` satisfies
conditions (1) and (2) of Stacks Definition 8.4.1. -/
@[stacks 04UA, instance]
instance instIsPrestackOnSite (S : Scheme.{u}) :
    IsPrestack.OnSite (Scheme.fppfTopology.over S) (p : Spaces S ⥤ Over S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
