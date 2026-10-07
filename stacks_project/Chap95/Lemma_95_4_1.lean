module

public import stacks_project.Chap95.«95_4_0_1_Category»
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-!
# Lemma 95.4.1

A morphism of `QCohStack` is strongly cartesian if and only if its sheaf
component is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.QCohStack

/-- Lemma 95.4.1: a morphism `(f, φ) : (Y, G) ⟶ (X, F)` of `QCohStack` is
strongly cartesian if and only if `φ` induces an isomorphism `f* F ⟶ G`. -/
@[stacks 04U3]
theorem isStronglyCartesian_iff_isIso_sheaf {S : Scheme.{u}} {x y : Obj S} (φ : x ⟶ y) :
    (p S).IsStronglyCartesian ((p S).map φ) φ ↔ IsIso φ.sheaf :=
  sorry

end AlgebraicGeometry.QCohStack
