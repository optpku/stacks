/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex.NaiveComparison
import StacksCheckRecall

/-!
# Comparison of the cotangent complex of a morphism of ringed spaces with the naive cotangent complex

Lemma 92.20.4 records the canonical cochain map `L[f] ⟶ NL[f]` identifying the naive
cotangent complex with the good truncation `τ_{≥ -1} L[f]`.
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

#check (AlgebraicGeometry.RingedSpace.toNaive :
  ∀ (f : X ⟶ Y), cotangentComplex f ⟶ naiveCotangent f)

/- Lemma 92.20.4. The canonical map identifies `NL[f]` with the truncation
`τ_{≥ -1} L[f]`. -/
@[stacks 08UW] #check (AlgebraicGeometry.RingedSpace.toNaive_truncGE_quasiIso :
  ∀ (f : X ⟶ Y), QuasiIso (CochainComplex.truncGEMap (toNaive f) (-1)))

#check (AlgebraicGeometry.RingedSpace.naiveCotangent_isGE_negOne :
  ∀ (f : X ⟶ Y), (naiveCotangent f).IsGE (-1))

end AlgebraicGeometry.RingedSpace

