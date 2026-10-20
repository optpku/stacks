/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Construction

/-!
# Morphisms between chosen relative spectra
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {A B : X.QcAlgebraUnder}

/-- The contravariant morphism of chosen relative spectra induced by an algebra morphism. -/
noncomputable def relativeSpecMap (f : A ⟶ B)
    (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver B) [IsRelativeSpectrumOver Q] :
    relativeSpec Q ⟶ relativeSpec P :=
  (IsRelativeSpectrumOver.isRepresentedBy (P := P)).representableBy.homEquiv.symm
    (⟨relativeSpecπ Q,
      (QcAlgebraUnder.forget X).map f ≫ relativeSpecUniversalFamily Q⟩ :
      relativeSpectrumPair A (relativeSpec Q))

/-- Pulling back the universal point along `relativeSpecMap` gives the point obtained by
precomposing the source universal family with the algebra morphism. -/
theorem relativeSpecMap_spec (f : A ⟶ B)
    (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver B) [IsRelativeSpectrumOver Q] :
    relativeSpectrumPairPullbackMap A (relativeSpecMap f P Q) (relativeSpecPoint P) =
      (⟨relativeSpecπ Q,
        (QcAlgebraUnder.forget X).map f ≫ relativeSpecUniversalFamily Q⟩ :
        relativeSpectrumPair A (relativeSpec Q)) := sorry

/-- The relative-spectrum morphism induced by an algebra map lies over the base scheme. -/
theorem relativeSpecMap_projection (f : A ⟶ B)
    (P : RelativeSpectrumOver A) [IsRelativeSpectrumOver P]
    (Q : RelativeSpectrumOver B) [IsRelativeSpectrumOver Q] :
    relativeSpecMap f P Q ≫ relativeSpecπ P = relativeSpecπ Q := sorry

end AlgebraicGeometry.Scheme
