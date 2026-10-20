/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Modification.PuncturedSpectrum

/-!
# Modifications of the spectrum of a 2-dimensional Noetherian local domain
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 89.2.1 Let `(A, 𝔪, κ)` be a 2-dimensional Noetherian local domain
such that `U = Spec(A) \ {𝔪}` is a normal scheme. Then any modification
`f : X ⟶ specSpace A` is a morphism as in 89.2.0.1: `f` is proper and
`f⁻¹(U) ⟶ U` is an isomorphism. -/
@[stacks 0AE3] #check
  (AlgebraicGeometry.AlgebraicSpace.isProperIsoOverOpen_puncturedι_of_isModification :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A],
      ringKrullDim A = 2 → (PuncturedSpectrum.scheme A).isNormal →
        ∀ {X : AlgebraicSpace (Spec (.of A))} [IsIntegral X]
          (f : X ⟶ specSpace A) [IsModification f],
          IsProperIsoOverOpen f (puncturedι A))
