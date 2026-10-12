/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence.Target

@[expose] public section

/-!
# 15.68.0.1 (0AVH)

@stack 0AVH
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

/- 15.68.0.1: for an `R`-module `M` and `K ∈ D⁺(R)`, the canonical target
hyper-Ext construction gives the cohomological spectral sequence
`E₂ⁱʲ = Extⁱ_R(M, Hʲ(K))` converging to `Extⁱ⁺ʲ_R(M, K)`. -/
@[stacks 0AVH "15.68.0.1 target hyper-Ext spectral sequence"]
#check
  fun (M : ModuleCat.{u} R) (K : DerivedCategory.Plus (ModuleCat.{u} R)) ↦
    (DerivedCategory.Ext.Target.Cohomology.existsSpectralSequence
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj M) K.obj :
      ∃ (F : FilteredComplex AddCommGrpCat.{u + 1})
        (E : CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 0)
        (E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1}),
        DerivedCategory.Ext.Target.Cohomology.IsSpectralSequence
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj M) K.obj F E E')

/- The second-page identification of the canonical target spectral sequence. -/
#check @DerivedCategory.Ext.Target.Cohomology.IsSpectralSequence.pageTwo

/- Boundedness under the source hypotheses `M[0] ∈ D⁻(R)` and `K ∈ D⁺(R)`. -/
#check @DerivedCategory.Ext.Target.Cohomology.IsSpectralSequence.bounded

/- The retained filtered complex realizes the Ext abutment through the canonical renumbering. -/
#check @DerivedCategory.Ext.Target.Cohomology.IsSpectralSequence.realizesViaRenumbering

/- Convergence of the displayed `E₂`-sequence under the same boundedness hypotheses. -/
#check @DerivedCategory.Ext.Target.Cohomology.IsSpectralSequence.convergesAfterRenumbering

end CategoryTheory
