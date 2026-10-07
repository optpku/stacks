module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree
public import ReasLib.CategoryTheory.Limits.Countable

@[expose] public section

/-!
# Basic Telescope Lifts for Semi-Free Filtrations

This leaf owns the explicit recursive degreewise lifts from filtration stages
into the telescope coproduct.  Computation after augmentation, sections, and
admissibility live in smaller dependent leaves.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CountableFromSequential

noncomputable section

universe u

namespace CochainComplex.SemiFreeFiltration

section

variable {A : Type u} [Ring A]

/-- The chosen retraction of a degree-`n` semi-free filtration step. -/
noncomputable def stepTermwiseRetraction {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (k : ℕ) (n : ℤ) :
    (F.stage (k + 1)).X n ⟶ (F.stage k).X n :=
  @retraction (ModuleCat A) _ _ _ ((F.inclusion k).f n) (stepTermwiseSplitMono F k n)

/-- The chosen retraction of a degreewise filtration step is a left inverse. -/
theorem stepTermwiseInclusion_retraction {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (k : ℕ) (n : ℤ) :
    (F.inclusion k).f n ≫ stepTermwiseRetraction F k n = 𝟙 ((F.stage k).X n) := sorry

variable [HasColimitsOfShape ℕ (ModuleCat.DGMod A)]

/-- The recursive finite-support lift of the `k`th filtration stage into the degree-`n` telescope
coproduct. -/
noncomputable def telescopeDegreewiseStageLift {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℤ) :
    ∀ k : ℕ, (F.stage k).X n ⟶
      (F.toSequentialColimitFiltration.telescopeShortComplex.X₂).X n
  | 0 => 0
  | k + 1 =>
      let previous :
          (F.stage (k + 1)).X n ⟶
            (F.toSequentialColimitFiltration.telescopeShortComplex.X₂).X n :=
        stepTermwiseRetraction F k n ≫ telescopeDegreewiseStageLift F n k
      let correction :
          (F.stage (k + 1)).X n ⟶
            (F.toSequentialColimitFiltration.telescopeShortComplex.X₂).X n :=
        (𝟙 _ - stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
          ((Limits.Sigma.ι F.toSequentialColimitFiltration.diagram.obj (k + 1)).f n)
      previous + correction

/-- The complement projector of a split filtration step is killed by that step. -/
theorem stepTermwiseProjectorCancellation {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (k : ℕ) (n : ℤ) :
    (F.inclusion k).f n ≫
        (𝟙 ((F.stage (k + 1)).X n) - stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) =
      0 := sorry

/-- Recursive degreewise stage lifts are compatible with successive filtration maps. -/
theorem telescopeDegreewiseStageLift_compat {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℤ) (k : ℕ) :
    (F.inclusion k).f n ≫ telescopeDegreewiseStageLift F n (k + 1) =
      telescopeDegreewiseStageLift F n k := sorry

/-- A degreewise telescope stage lift followed by a later prefix projection is the corresponding
transition map of the evaluated filtration. -/
theorem telescopeDegreewiseStageLift_comp_prefixProjection_of_le
    {P : ModuleCat.DGMod A} (F : SemiFreeFiltration P) (n : ℤ)
    {k m : ℕ} (hkm : k ≤ m) :
    telescopeDegreewiseStageLift F n k ≫
        (Limits.Sequential.prefixProjection F.toSequentialColimitFiltration.diagram m).f n =
      (F.toSequentialColimitFiltration.diagram ⋙
        HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n).map (homOfLE hkm) := sorry

/-- A degreewise telescope stage lift is a section of the matching prefix projection. -/
theorem telescopeDegreewiseStageLift_comp_prefixProjection_self
    {P : ModuleCat.DGMod A} (F : SemiFreeFiltration P) (n : ℤ) (k : ℕ) :
    telescopeDegreewiseStageLift F n k ≫
        (Limits.Sequential.prefixProjection F.toSequentialColimitFiltration.diagram k).f n =
      𝟙 ((F.stage k).X n) := sorry

end

end CochainComplex.SemiFreeFiltration
