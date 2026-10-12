/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree.Telescope.Section

@[expose] public section

/-!
# Admissible Telescope Sequences

This leaf packages the exactness, degreewise splitting, and admissibility
consequences of the telescope of a semi-free filtration.
-/

open CategoryTheory CategoryTheory.Limits
open scoped CountableFromSequential

noncomputable section

universe u

namespace CochainComplex.SemiFreeFiltration

section

variable {A : Type u} [Ring A]
variable [HasColimitsOfShape ℕ (ModuleCat.DGMod A)]

/-- Evaluating the telescope short exact sequence in degree `n` produces a short exact sequence
of `A`-modules. -/
theorem telescopeDegreewiseShortExact
    [HasExactColimitsOfShape ℕ (CochainComplex (ModuleCat.{u} A) ℤ)]
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (F : SemiFreeFiltration P) (n : ℤ) :
    (F.toSequentialColimitFiltration.telescopeShortComplex.map
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)).ShortExact := sorry

/-- The evaluated telescope short complex is split by the descended degreewise section. -/
noncomputable def telescopeDegreewiseSplitting
    [HasExactColimitsOfShape ℕ (CochainComplex (ModuleCat.{u} A) ℤ)]
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (F : SemiFreeFiltration P) (n : ℤ)
    [PreservesColimitsOfShape ℕ
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)] :
    (ShortComplex.degreewise F.toSequentialColimitFiltration.telescopeShortComplex n).Splitting :=
  ShortComplex.Splitting.ofExactOfSection
      (F.toSequentialColimitFiltration.telescopeShortComplex.map
        (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n))
      (telescopeDegreewiseShortExact F n).exact
      (telescopeDegreewiseSection F n)
      (telescopeDegreewiseSection_rightInv F n)
      (telescopeDegreewiseShortExact F n).mono_f

/-- The telescope short exact sequence of a semi-free filtration is admissible after forgetting
cochain differentials. -/
instance instTelescopeIsAdmissibleShortExact
    [HasExactColimitsOfShape ℕ (ModuleCat.DGMod A)]
    [PreservesColimitsOfShape (Discrete ℕ) (dgModuleUnderlyingGradedHomSystem (A := A))]
    [PreservesColimitsOfShape ℕ (dgModuleUnderlyingGradedHomSystem (A := A))]
    [hEval : ∀ n : ℤ, PreservesColimitsOfShape ℕ
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)]
    {P : ModuleCat.DGMod A} (F : SemiFreeFiltration P) :
    IsAdmissibleShortExact (dgModuleUnderlyingGradedHomSystem (A := A))
      F.toSequentialColimitFiltration.telescopeShortComplex := sorry

/-- A semi-free filtration induces an admissible telescope short exact sequence after forgetting
cochain differentials. -/
theorem telescope_isAdmissibleShortExact
    [HasExactColimitsOfShape ℕ (ModuleCat.DGMod A)]
    [PreservesColimitsOfShape (Discrete ℕ) (dgModuleUnderlyingGradedHomSystem (A := A))]
    [PreservesColimitsOfShape ℕ (dgModuleUnderlyingGradedHomSystem (A := A))]
    [hEval : ∀ n : ℤ, PreservesColimitsOfShape ℕ
      (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n)]
    {P : ModuleCat.DGMod A} (F : SemiFreeFiltration P) :
    IsAdmissibleShortExact (dgModuleUnderlyingGradedHomSystem (A := A))
      F.toSequentialColimitFiltration.telescopeShortComplex := sorry

end

end CochainComplex.SemiFreeFiltration
