/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.Fin
public import ReasLib.RingTheory.MvPolynomial.Finite
public import ReasLib.RingTheory.MvPolynomial.FiniteVariables
public import ReasLib.RingTheory.MvPolynomial.FractionRing
public import ReasLib.RingTheory.MvPolynomial.Coordinate
public import ReasLib.RingTheory.MvPolynomial.Homogenization
public import ReasLib.RingTheory.MvPolynomial.Homogenization.PositiveQuotient
public import ReasLib.RingTheory.MvPolynomial.Localization
public import ReasLib.RingTheory.MvPolynomial.Localization.GenericFiber
public import ReasLib.RingTheory.MvPolynomial.Localization.GenericFiber.Module
public import ReasLib.RingTheory.MvPolynomial.Localization.Module
public import ReasLib.RingTheory.MvPolynomial.Localization.Module.Equiv
public import ReasLib.RingTheory.MvPolynomial.Localization.Module.FinitePresentation
public import ReasLib.RingTheory.MvPolynomial.Localization.Module.Free
public import ReasLib.RingTheory.MvPolynomial.Localization.Quotient
public import ReasLib.RingTheory.MvPolynomial.Nilpotent
public import ReasLib.RingTheory.MvPolynomial.Noetherian
public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.FactorizationAway
public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Prime
public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Quotient
public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Shear
public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Triangular
public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Weights
public import ReasLib.RingTheory.MvPolynomial.Quotient
public import ReasLib.RingTheory.MvPolynomial.Solution

/-!
# Multivariate Polynomial Infrastructure

Aggregate entry point for reusable multivariate-polynomial constructions.
Import a child leaf directly when only one construction is needed.
-/
