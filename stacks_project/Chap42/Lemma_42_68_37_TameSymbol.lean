/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.DiscreteValuationRing.Formula

@[expose] public section

open scoped nonZeroDivisors

universe u v

variable (A : Type u) (K : Type v) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]

/- The usual tame symbol of a discrete valuation ring is the residue of its signed
valuation-zero ratio, bundled as a bimultiplicative map. -/
#check (DVR.TameSymbol.value A K :
  Kˣ →* (Kˣ →* (IsLocalRing.ResidueField A)ˣ))
