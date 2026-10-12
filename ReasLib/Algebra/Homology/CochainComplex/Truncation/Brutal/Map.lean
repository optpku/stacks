/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Trunc

/-!
# Computation rules for brutal tower maps

The filtration-stage and `stupidTrunc` presentations expose the same
componentwise map API.  This leaf supplies the missing component abbreviation
and identity/composition rewrites for the filtration-stage presentation, and
the corresponding component rewrites for the transported presentation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Stage

/-- A cochain-complex identity acts as the identity on every brutal stage. -/
@[simp, stacks 0D8Z]
theorem map_id (K : CochainComplex A ℤ) (p : ℤ) :
    map (𝟙 K) p = 𝟙 (obj K p) := sorry

/-- Brutal stage maps preserve composition. -/
@[simp, stacks 0D8Z]
theorem map_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) (p : ℤ) :
    map (f ≫ g) p = map f p ≫ map g p := sorry

/-- A brutal-stage map is evaluated by the filtered-object stage map in each degree. -/
@[simp, stacks 0D8Z]
theorem map_f {K L : CochainComplex A ℤ} (f : K ⟶ L) (p i : ℤ) :
    (map f p).f i = ((Stupid.map f).f i).stageMap p := sorry

end Stage

namespace Tower

/-- The map on the `n`th filtration-stage brutal tower component. -/
noncomputable abbrev mapApp {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    obj K n ⟶ obj L n :=
  Stage.map f (index n)

/-- The bundled tower map evaluates to its component map. -/
@[simp, stacks 0D8Z]
theorem mapApp_eq_map_app {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (map f).app n = mapApp f n := sorry

/-- A cochain-complex identity acts as the identity on each filtration-stage component. -/
@[simp, stacks 0D8Z]
theorem mapApp_id (K : CochainComplex A ℤ) (n : ℕ) :
    mapApp (𝟙 K) n = 𝟙 (obj K n) := sorry

/-- Filtration-stage component maps preserve composition. -/
@[simp, stacks 0D8Z]
theorem mapApp_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) :
    mapApp (f ≫ g) n = mapApp f n ≫ mapApp g n := sorry

/-- A filtration-stage tower component is evaluated by the corresponding filtered-object stage map. -/
@[simp, stacks 0D8Z]
theorem mapApp_f {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) (i : ℤ) :
    (mapApp f n).f i = ((Stupid.map f).f i).stageMap (index n) := sorry

/-- The filtration-stage tower map of an identity is the identity transformation. -/
@[simp, stacks 0D8Z]
theorem map_id (K : CochainComplex A ℤ) :
    map (𝟙 K) = 𝟙 (diagram K) := sorry

/-- Filtration-stage tower maps preserve composition. -/
@[simp, stacks 0D8Z]
theorem map_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = map f ≫ map g := sorry

end Tower

namespace Trunc

/-- A `stupidTrunc` component map preserves identities. -/
@[simp, stacks 0D8Z]
theorem mapApp_id (K : CochainComplex A ℤ) (n : ℕ) :
    mapApp (𝟙 K) n = 𝟙 (obj K n) := sorry

/-- A `stupidTrunc` component map preserves composition. -/
@[simp, stacks 0D8Z]
theorem mapApp_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) (n : ℕ) :
    mapApp (f ≫ g) n = mapApp f n ≫ mapApp g n := sorry

end Trunc

end CategoryTheory.CochainComplex.Brutal
