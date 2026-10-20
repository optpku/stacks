/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Immersion

/-!
# Finite presentation of Fitting loci

The closed, open, and successive locally closed loci defined by the Fitting
filtration of a finitely presented module are of finite presentation.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A closed subscheme cut out by a Fitting ideal sheaf of a finitely presented module is of
finite presentation over the ambient scheme. -/
theorem fittingClosedSubscheme_hom_finitePresentation
    {S : Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation] (r : ℕ) :
    Hom.FinitePresentation (fittingIdealSheaf F r).subschemeι := sorry

/-- The complement of a Fitting closed subscheme of a finitely presented module is of finite
presentation over the ambient scheme. -/
theorem fittingOpenComplement_hom_finitePresentation
    {S : Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation] (r : ℕ) :
    Hom.FinitePresentation (fittingOpenComplement F r).ι := sorry

/-- Every successive Fitting rank locus of a finitely presented module is of finite
presentation over the ambient scheme. -/
theorem fittingRankLocus_hom_finitePresentation
    {S : Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation] (r : ℕ) :
    Hom.FinitePresentation (fittingRankLocusι F r) := sorry

end AlgebraicGeometry.Scheme
