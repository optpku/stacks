module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree.Telescope.Computation

@[expose] public section

/-!
# Degreewise Telescope Sections

This leaf descends the explicit stage lifts to sections of the telescope
augmentation and exposes the resulting monomorphism API for filtration legs.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CountableFromSequential

noncomputable section

universe u

namespace CochainComplex.SemiFreeFiltration

section

variable {A : Type u} [Ring A]
variable [HasColimitsOfShape ℕ (ModuleCat.DGMod A)]

/-- Descending degreewise stage lifts along the evaluated colimit cocone gives a section of the
telescope augmentation. -/
noncomputable def telescopeDegreewiseSection {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℤ)
    [PreservesColimitsOfShape ℕ
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)] :
    P.X n ⟶ (F.toSequentialColimitFiltration.telescopeShortComplex.X₂).X n :=
  (isColimitOfPreserves
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)
      F.toSequentialColimitFiltration.isColimit).desc
    (telescopeDegreewiseLiftCocone F n)

/-- On each filtration stage, the descended degreewise section agrees with the recursive lift. -/
theorem telescopeDegreewiseSection_fac {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℤ) (k : ℕ)
    [PreservesColimitsOfShape ℕ
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)] :
    (F.coconeApp k).f n ≫ telescopeDegreewiseSection F n =
      telescopeDegreewiseStageLift F n k := sorry

/-- The descended degreewise section is a right inverse to the telescope augmentation. -/
theorem telescopeDegreewiseSection_rightInv {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℤ)
    [PreservesColimitsOfShape ℕ
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)] :
    telescopeDegreewiseSection F n ≫
        ((F.toSequentialColimitFiltration.telescopeShortComplex.g).f n) =
      𝟙 (P.X n) := sorry

/-- Every cocone leg of a semi-free filtration is monic when evaluation preserves its sequential
colimit. -/
theorem coconeApp_mono
    [hEval : ∀ n : ℤ, PreservesColimitsOfShape ℕ
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)]
    {P : ModuleCat.DGMod A} (F : SemiFreeFiltration P) (k : ℕ) :
    Mono (F.coconeApp k) := sorry

end

end CochainComplex.SemiFreeFiltration
