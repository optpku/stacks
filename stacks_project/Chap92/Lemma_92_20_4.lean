module

public import stacks_project.Chap92.Definition_92_20_1_Morphism
public import stacks_project.Chap92.Lemma_92_18_10_Comparison
import Mathlib.Tactic.CrossRefAttribute

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

/-- Lemma 92.20.4 (1). Let `f : (X, O_X) ⟶ (Y, O_Y)` be a morphism of ringed spaces.
There is a canonical cochain map `L[f] ⟶ NL[f]`. -/
@[stacks 08UW]
noncomputable abbrev toNaive (f : X ⟶ Y) :
    cotangentComplex f ⟶ naiveCotangent f :=
  CotangentComplex.toNaive _ (inverseImageStructureSheafUnder f)

/-- Lemma 92.20.4 (2). The canonical map identifies `NL[f]` with the truncation
`τ_{≥ -1} L[f]`. -/
@[stacks 08UW]
instance toNaive_truncGE_quasiIso (f : X ⟶ Y) :
    QuasiIso (CochainComplex.truncGEMap (toNaive f) (-1)) :=
  sorry

/-- The naive cotangent complex of a morphism of ringed spaces is concentrated in degrees
`≥ -1`, so `τ_{≥ -1}` recovers `NL[f]`. -/
instance naiveCotangent_isGE_negOne (f : X ⟶ Y) :
    (naiveCotangent f).IsGE (-1) :=
  sorry

end AlgebraicGeometry.RingedSpace

