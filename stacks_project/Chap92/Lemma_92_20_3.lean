module

public import stacks_project.Chap92.Lemma_92_20_3_Triangle
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity triangle of the cotangent complex of a morphism of ringed spaces

Lemma 92.20.3 records that morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of ringed spaces
induce a canonical distinguished triangle
`Lf^* L[g] ⟶ L[f ≫ g] ⟶ L[f] ⟶ Lf^* L[g]⟦1⟧` in `D(O_X)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y Z : RingedSpace.{u}}
variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Lemma 92.20.3. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces.
Then there is a canonical distinguished triangle
`Lf^* L[g] ⟶ L[f ≫ g] ⟶ L[f] ⟶ Lf^* L[g]⟦1⟧`
in `D(O_X)`, displayed on the underived vertex `pullbackCotangent f g ≅
(modulePullbackDerived f).obj (derived g)` via `pullbackIso_derived` and
`pullbackIso_inverseImage`, using termwise flatness of `f⁻¹ L[g]` from Lemma 92.18.3. -/
@[stacks 08T4]
theorem transitivityTriangle_distinguished :
    transitivityTriangle f g ∈ distTriang (DerivedCategory X.Modules) :=
  sorry

end AlgebraicGeometry.RingedSpace
