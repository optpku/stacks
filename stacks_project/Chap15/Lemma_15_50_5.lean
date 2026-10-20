/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.GRing.MixedPowerSeriesPolynomial
import StacksCheckRecall

/-!
# Lemma 15.50.5

@stack 07PR
-/

@[expose] public section

open FieldExtension.PBasis

-- Lemma 15.50.5 (07PR): the generic formal fiber of
-- `k[[x₁, …, xₙ]][y₁, …, yₘ]` is geometrically regular over its fraction field.
@[stacks 07PR "mixed power-series/polynomial formal fiber"]
#check @mixedPowerSeriesPolynomialRing.formalFiber_fractionRing_isGeometricallyRegular
