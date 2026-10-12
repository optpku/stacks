/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.«98_13_2_1_Smooth»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of smoothness on predeformations

Smoothness on associated predeformations is stable under composition of
1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 98.13.4: if `S` is locally Noetherian and `f : X ⟶ Y`, `g : Y ⟶ Z`
are composable 1-morphisms of categories fibred in groupoids over
`(Sch/S)_fppf` that are smooth on predeformations (98.13.2.1), then so is
`f ≫ g` (source `g ∘ f`). -/
@[stacks 07XU]
instance IsSmoothOnPredeformations.comp
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSmoothOnPredeformations f] [IsSmoothOnPredeformations g] :
    IsSmoothOnPredeformations (f ≫ g) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
