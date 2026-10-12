/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree

/-!
# Fibre-degree bounds and base change

This file establishes preservation of uniform fibre-degree bounds under base
change and their descent along surjective base change.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y Y' : Scheme.{u}}

/-- A fixed bound on fibre degrees is preserved by arbitrary base change. -/
theorem degreesOfFibresBoundedBy_baseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y) {n : ℕ}
    (h : degreesOfFibresBoundedBy f n) :
    degreesOfFibresBoundedBy (pullback.snd f g) n := sorry

/-- Universal boundedness of fibre degrees is preserved by arbitrary base change. -/
theorem universallyBoundedFibres_baseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : universallyBoundedFibres f) :
    universallyBoundedFibres (pullback.snd f g) := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, degreesOfFibresBoundedBy_baseChange f g hn⟩

/-- A fixed fibre-degree bound after a surjective base change also bounds the original
morphism. -/
theorem degreesOfFibresBoundedBy_of_surjective_baseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y) [Surjective g] {n : ℕ}
    (h : degreesOfFibresBoundedBy (pullback.snd f g) n) :
    degreesOfFibresBoundedBy f n := sorry

/-- Universal boundedness of fibre degrees descends along a surjective base change. -/
theorem universallyBoundedFibres_of_surjective_baseChange
    (f : X ⟶ Y) (g : Y' ⟶ Y) [Surjective g]
    (h : universallyBoundedFibres (pullback.snd f g)) :
    universallyBoundedFibres f := by
  rcases h with ⟨n, hn⟩
  exact ⟨n, degreesOfFibresBoundedBy_of_surjective_baseChange f g hn⟩

end Scheme.Hom
end AlgebraicGeometry
