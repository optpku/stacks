module

import StacksCheckRecall
public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Target

@[expose] public section

/-!
# 15.68.0.2 (0AVI)

@stack 0AVI
-/

open CategoryTheory
open scoped CategoryTheory DerivedExt

noncomputable section

universe u

-- Local instance justification (defeq pin): the source-facing spectral sequence is stated in
-- Mathlib's standard derived-category model, which is not installed globally for `ModuleCat R`.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

variable {R : Type u} [Ring R]
  [IsGrothendieckAbelian.{u} (ModuleCat.{u} R)]

/- 15.68.0.2: for an `R`-module `M` and a bounded-below cochain complex `K`, the
stupid filtration gives the target hyper-Ext spectral sequence
`E₁ᵖʸ = Extʸ_R(M, Kᵖ)` converging to `Extᵖ⁺ʸ_R(M, K)`. -/
@[stacks 0AVI "15.68.0.2 stupid-filtration hyper-Ext spectral sequence"]
#check
  fun (M : ModuleCat.{u} R) (K : CochainComplex (ModuleCat.{u} R) ℤ) ↦
    (DerivedCategory.Ext.Target.Stupid.existsSpectralSequence
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj M) K :
      ∃ (F : FilteredComplex AddCommGrpCat.{u + 1})
        (E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0),
        DerivedCategory.Ext.Target.Stupid.IsSpectralSequence
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj M) K F E)

/- The first-page identification `E₁ᵖʸ = Extʸ_R(M, Kᵖ)`. -/
#check @DerivedCategory.Ext.Target.Stupid.IsSpectralSequence.pageOne

/- Boundedness for `M[0] ∈ D⁻(R)` and a bounded-below representative `K`. -/
#check @DerivedCategory.Ext.Target.Stupid.IsSpectralSequence.bounded

/- Convergence of the associated filtered complex to total Ext. -/
#check @DerivedCategory.Ext.Target.Stupid.IsSpectralSequence.converges

end CategoryTheory
