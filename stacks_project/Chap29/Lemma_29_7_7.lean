/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.SchemeTheoreticImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.7.7 (1): if `h : Z ⟶ X` is an immersion and either `h` is quasi-compact or `Z`
is reduced, then the canonical map from `Z` to the scheme-theoretic image of `h` is an open
immersion. -/
@[stacks 01RG] #check
  (AlgebraicGeometry.Scheme.Hom.isOpenImmersion_toImage_of_quasiCompact_or_isReduced :
    ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (h : Z ⟶ X) [AlgebraicGeometry.IsImmersion h],
      AlgebraicGeometry.QuasiCompact h ∨ AlgebraicGeometry.IsReduced Z →
        AlgebraicGeometry.IsOpenImmersion h.toImage)

/- Lemma 29.7.7 (2): under the same hypotheses, the open range of the canonical map from `Z`
to the scheme-theoretic image of `h` is scheme-theoretically dense. -/
@[stacks 01RG] #check
  (AlgebraicGeometry.Scheme.Hom.schemeTheoreticallyDense_opensRange_toImage_of_quasiCompact_or_isReduced :
    ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (h : Z ⟶ X) [AlgebraicGeometry.IsImmersion h]
      (hqc_or_red : AlgebraicGeometry.QuasiCompact h ∨ AlgebraicGeometry.IsReduced Z),
      AlgebraicGeometry.schemeTheoreticallyDense
        (@AlgebraicGeometry.Scheme.Hom.opensRange _ _ h.toImage
          (AlgebraicGeometry.Scheme.Hom.isOpenImmersion_toImage_of_quasiCompact_or_isReduced
            h hqc_or_red)))

/- Lemma 29.7.7 (3): under the same hypotheses, the canonical map from `Z` to the
scheme-theoretic image of `h` is dominant, so `Z` is topologically dense in that image. -/
@[stacks 01RG] #check
  (AlgebraicGeometry.Scheme.Hom.isDominant_toImage_of_quasiCompact_or_isReduced :
    ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (h : Z ⟶ X) [AlgebraicGeometry.IsImmersion h],
      AlgebraicGeometry.QuasiCompact h ∨ AlgebraicGeometry.IsReduced Z →
        AlgebraicGeometry.IsDominant h.toImage)
