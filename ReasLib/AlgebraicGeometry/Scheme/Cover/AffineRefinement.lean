/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

universe u v

namespace AlgebraicGeometry.Scheme

/-- A finite affine refinement over every affine target open makes a family of
scheme morphisms jointly surjective. -/
theorem jointlySurjective_of_affineRefinement {T : Scheme.{u}} {ι : Type v}
    (domains : ι → Scheme.{u}) (maps : ∀ index, domains index ⟶ T)
    (h_refinement : ∀ targetOpen : T.Opens, IsAffineOpen targetOpen →
      ∃ count : ℕ, ∃ indices : Fin count → ι,
        ∃ sourceOpens : (position : Fin count) → (domains (indices position)).Opens,
          (∀ position, IsAffineOpen (sourceOpens position)) ∧
            (⋃ position, maps (indices position) ''
              (sourceOpens position : Set (domains (indices position)))) =
              (targetOpen : Set T)) :
    ∀ point : T, ∃ index : ι, ∃ preimage : domains index, maps index preimage = point := sorry

end AlgebraicGeometry.Scheme
