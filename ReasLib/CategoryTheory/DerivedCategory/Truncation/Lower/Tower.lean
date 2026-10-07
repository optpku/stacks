module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.CategoryTheory.Triangulated.TStructure.TruncGE.Sequence

@[expose] public section

/-!
# The Lower Derived-Truncation Tower

For a derived object `K`, this leaf owns the canonical sequential inverse
system `n ↦ τ≥(-n) K`, its transition maps, and the canonical maps from `K`
to its stages. It uses the canonical derived-category `t`-structure and does
not select a product or a derived-limit presentation.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Triangulated.TStructure.TruncGE
open DerivedCategory.TStructure

universe w v u

namespace CategoryTheory.DerivedCategory.Truncation.Lower

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The integer indexing the `n`th lower derived truncation. -/
@[stacks 0H72]
abbrev index (n : ℕ) : ℤ :=
  -(n : ℤ)

/-- The standard lower-truncation cutoff sequence is antitone. -/
@[stacks 0H72]
theorem index_antitone : Antitone index := sorry

/-- Consecutive indices of the lower truncation tower are ordered in the
direction required for the transition map. -/
@[stacks 0H72]
theorem index_succ_le (n : ℕ) :
    index (n + 1) ≤ index n := sorry

/-- The `n`th stage `τ≥(-n) K` of the lower
derived-truncation tower. -/
@[stacks 0H72]
noncomputable abbrev stage (K : DerivedCategory 𝒜) (n : ℕ) :
    DerivedCategory 𝒜 :=
  Sequence.stage t K index n

/-- The transition morphism from the successor lower
truncation stage to the preceding stage. -/
@[stacks 0H72]
noncomputable abbrev step (K : DerivedCategory 𝒜) (n : ℕ) :
    stage K (n + 1) ⟶ stage K n :=
  Sequence.step t K index
    (fun _ _ h ↦ neg_le_neg (Int.ofNat_le_ofNat_of_le h)) n

/-- The sequential inverse system `n ↦ τ≥(-n) K` in the
derived category. -/
@[stacks 0H72]
noncomputable def tower (K : DerivedCategory 𝒜) :
    SequentialInverseSystem (DerivedCategory 𝒜) :=
  Sequence.ofAntitone t K index
    (fun _ _ h ↦ neg_le_neg (Int.ofNat_le_ofNat_of_le h))

/-- A lower tower stage computes to the corresponding canonical lower
truncation. -/
@[simp, stacks 0H72]
theorem tower_obj (K : DerivedCategory 𝒜) (n : ℕ) :
    (tower K).obj (op n) = stage K n := sorry

/-- The successor map of the lower tower is its declared truncation
comparison. -/
@[simp, stacks 0H72]
theorem tower_stepMap (K : DerivedCategory 𝒜) (n : ℕ) :
    (tower K).stepMap n = step K n := sorry

/-- Every transition of the lower tower is the direct canonical comparison
between its endpoint truncations. -/
@[stacks 0H72]
theorem tower_transitionMap (K : DerivedCategory 𝒜) {m n : ℕ} (h : m ≤ n) :
    (tower K).transitionMap h =
      (t.natTransTruncGEOfLE (index n) (index m)
        (neg_le_neg (Int.ofNat_le_ofNat_of_le h))).app K := sorry

/-- The canonical map from `K` to the `n`th stage of its lower
derived-truncation tower. -/
@[stacks 0H72]
noncomputable abbrev toStage (K : DerivedCategory 𝒜) (n : ℕ) :
    K ⟶ (tower K).obj (op n) :=
  (t.truncGEπ (index n)).app K

/-- The canonical maps from `K` to its lower truncations commute with the
successor transition maps of the tower. -/
@[reassoc (attr := simp), stacks 0H72]
theorem toStage_comp_transition (K : DerivedCategory 𝒜) (n : ℕ) :
    toStage K (n + 1) ≫ (tower K).transitionMap (Nat.le_succ n) =
      toStage K n := sorry

end CategoryTheory.DerivedCategory.Truncation.Lower
