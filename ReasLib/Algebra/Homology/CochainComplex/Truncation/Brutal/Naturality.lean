module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Map
public import ReasLib.CategoryTheory.Filtration.Complex.NegStage.Naturality

/-!
# Naturality of brutal tower transitions

This leaf records the successor square for the filtration-stage brutal tower.
The `stupidTrunc` transport already owns its analogous statement in
`Brutal.Trunc`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal.Tower

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Successor inclusions in the filtration-stage brutal tower are natural in the
cochain complex. -/
@[reassoc, stacks 0D8Z]
theorem step_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    step K n ≫ mapApp f (n + 1) = mapApp f n ≫ step L n := sorry

/-- The map of brutal-stage diagrams satisfies the successor naturality equation. -/
@[reassoc, stacks 0D8Z]
theorem map_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (diagram K).map (homOfLE (Nat.le_add_right n 1)) ≫ mapApp f (n + 1) =
      mapApp f n ≫ (diagram L).map (homOfLE (Nat.le_add_right n 1)) := sorry

end CategoryTheory.CochainComplex.Brutal.Tower
