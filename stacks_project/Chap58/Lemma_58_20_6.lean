/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 58.20.6: in Situation 58.19.1, if `V` is finite étale over `U`, a
power of `f` annihilates `H¹_𝔪(A)` and `H²_𝔪(A)`, and `V₀` is isomorphic to
`Y₀ ×_{X₀} U₀` for some finite étale `Y₀ → X₀`, then `V` is isomorphic to
`Y ×_X U` for some finite étale `Y → X`. -/
@[stacks 0BLS] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtale_extends_of_localCohomology_annihilation :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    (hH1 : Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
      ((localCohomology (maximalIdeal A) 1).obj (ModuleCat.of A A)))
    (hH2 : Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
      ((localCohomology (maximalIdeal A) 2).obj (ModuleCat.of A A)))
    (V : Scheme.FiniteEtale (scheme A))
    (Y0 : Scheme.FiniteEtale (Spec (CommRingCat.of (A ⧸ principalIdeal (f : A)))))
    (hV0 : Nonempty
      ((Scheme.finiteEtaleBaseChange (principalQuotientMap f)).obj V ≅
        (Scheme.finiteEtaleBaseChange
          (puncturedOpen (A ⧸ principalIdeal (f : A))).ι).obj Y0))
    , ∃ Y : Scheme.FiniteEtale (Spec (CommRingCat.of A)),
      Nonempty ((Scheme.finiteEtaleBaseChange (puncturedOpen A).ι).obj Y ≅ V))

end AlgebraicGeometry.PuncturedSpectrum
