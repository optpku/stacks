module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompletedDualResolution
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic

@[expose] public section
open CategoryTheory
noncomputable section
universe v u

namespace ActualCurveHomSign

/-- The four-periodic sign (-1)^((2-i)(1-i)/2), normalized to +1 in
degree 2. The residue formula also covers negative cochain degrees. -/
def phase (i : ℤ) : ℤ := if i % 4 = 1 ∨ i % 4 = 2 then 1 else -1

@[simp] theorem phase_square (i : ℤ) : phase i * phase i = 1 := by
  unfold phase
  split_ifs <;> norm_num

/-- Adjacent components introduce precisely the Hom differential sign. -/
theorem phase_step (i : ℤ) : phase (i + 1) * phase i =
    if (i + 1) % 2 = 0 then 1 else -1 := by
  unfold phase
  split_ifs <;> omega

/-- Hom into a single complex in degree 2 has differential
(-1)^(i+1) times precomposition by the original differential. -/
theorem phase_step_negOnePow (i : ℤ) : phase (i + 1) * phase i =
    ((i + 1).negOnePow : ℤ) := by
  rw [phase_step]
  split_ifs with h
  · have he : Even (i + 1) := Int.even_iff.mpr h
    rw [Int.negOnePow_even _ he]
    rfl
  · have ho : Odd (i + 1) := Int.odd_iff.mpr (by omega)
    rw [Int.negOnePow_odd _ ho]
    rfl

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : CochainComplex C ℤ)

/-- Change only the explicit differential signs. Objects and coefficient
actions remain those of K. No commutativity of a coefficient ring is used. -/
abbrev signed : CochainComplex C ℤ where
  X := K.X
  d i j := (phase j * phase i) • K.d i j
  shape i j h := by simp [K.shape i j h]
  d_comp_d' i j l _ _ := by
    simp

/-- On adjacent degrees the changed differential is the actual Hom sign. -/
theorem signed_d (i : ℤ) : (signed K).d i (i + 1) =
    ((i + 1).negOnePow : ℤ) • K.d i (i + 1) := by
  change (phase (i + 1) * phase i) • _ = _
  rw [phase_step_negOnePow]

/-- Both directions use the same involutive component sign. -/
def componentIso (i : ℤ) : K.X i ≅ (signed K).X i where
  hom := phase i • 𝟙 _
  inv := phase i • 𝟙 _
  hom_inv_id := by
    simp [smul_smul]
  inv_hom_id := by
    simp [smul_smul]

/-- The specified signs, not an arbitrary complex isomorphism. -/
def iso : K ≅ signed K := HomologicalComplex.Hom.isoOfComponents
  (componentIso K) (fun i j _ ↦ by
    dsimp [componentIso, signed]
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp,
      Category.comp_id, smul_smul]
    congr 1
    calc
      phase j * phase i * phase i = phase j * (phase i * phase i) := by ring
      _ = phase j := by rw [phase_square, mul_one])

/-- The chosen normalization leaves the top trace unchanged. -/
theorem top_component : (iso K).hom.f 2 = 𝟙 (K.X 2) := by
  change phase 2 • 𝟙 _ = _
  norm_num [phase]

end ActualCurveHomSign
