/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import StacksCheckRecall

/-!
# Constructible images of finitely presented quotients

@stack 00FA
-/

@[expose] public section

@[stacks 00FA "constructible image owner"]
#check @PrimeSpectrum.isConstructible_comap_image

@[stacks 00FA "finite-presentation map criterion"]
#check @RingHom.finitePresentation_algebraMap

@[stacks 00FA "finitely generated quotient presentation"]
#check @Algebra.FinitePresentation.quotient
