/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.«97_6_0_1_Lifting»

/-!
# Composition of morphisms formally smooth on objects

The composition of 1-morphisms of categories fibred in groupoids that are
formally smooth on objects is again formally smooth on objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace FormallySmoothOnObjects

/-- Lemma 97.6.2: If `p : X ⟶ Y` and `q : Y ⟶ Z` are 1-morphisms of categories
fibred in groupoids over `(Sch/S)_fppf` and both are formally smooth on objects,
then so is the composition `q ∘ p`, written `p ≫ q`. -/
@[stacks 06D2]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Y ⟶ Z) [FormallySmoothOnObjects p]
    [FormallySmoothOnObjects q] :
    FormallySmoothOnObjects (p ≫ q) := sorry

end FormallySmoothOnObjects

end AlgebraicGeometry.Groupoids.Hom
