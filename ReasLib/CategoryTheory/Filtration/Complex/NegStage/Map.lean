/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.NegStage

/-!
# Computation rules for negative filtration-stage maps

This leaf owns the identity and composition formulas for the component and
bundled maps in the negative-stage facade.  It is deliberately independent of
the successor naturality leaf so clients that only rewrite maps can import a
small module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.NegStage

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- A filtered-complex identity acts as the identity on every negative stage. -/
@[simp, stacks 0D8Z]
theorem mapApp_id (K : FilteredComplex A) (n : ℕ) :
    mapApp (𝟙 K) n = 𝟙 (obj K n) := sorry

/-- Stage maps on a composite filtered-complex morphism compose componentwise. -/
@[simp, stacks 0D8Z]
theorem mapApp_comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) :
    mapApp (f ≫ g) n = mapApp f n ≫ mapApp g n := sorry

/-- The negative-stage diagram map of an identity is the diagram identity. -/
@[simp, stacks 0D8Z]
theorem map_id (K : FilteredComplex A) :
    map (𝟙 K) = 𝟙 (diagram K) := sorry

/-- The negative-stage diagram map preserves composition. -/
@[simp, stacks 0D8Z]
theorem map_comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = map f ≫ map g := sorry

end CategoryTheory.FilteredComplex.NegStage
