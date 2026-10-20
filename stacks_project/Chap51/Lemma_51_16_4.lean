/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.Dualizing

@[expose] public section

open CategoryTheory CategoryTheory.Limits DerivedCategory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/- Lemma 51.16.4: let `A` be a Noetherian local ring with normalized dualizing
complex `ω`, and let `I` be an ideal of `A`. If degree-zero local cohomology of
`ω` supported on `V(I)` vanishes, then the local-cohomological dimension of `I`
is strictly less than `ringKrullDim A`. -/
@[stacks 0EB4] #check
  (Ideal.LocalCohomology.dimension_lt_ringKrullDim_of_degreeZero_isZero :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))],
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))] →
      (comparison :
        CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison (A := A)) →
      (ω : DerivedCategory (ModuleCat.{u} A)) →
      (hω : ω.IsNormalizedDualizingComplex comparison.closed) → (I : Ideal A) →
      (RΓ : DerivedCategory (ModuleCat A) ⥤ DerivedCategory.IdealPowerTorsion I) →
      (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ) →
      (h_vanish : IsZero
        ((homologyFunctor (ModuleCat A) 0).obj (RΓ.obj ω).obj)) →
    (dimension I I.fg_of_isNoetherianRing : EInt) <
      WithBot.map (WithTop.map Int.ofNat) (ringKrullDim A))

end Ideal.LocalCohomology
