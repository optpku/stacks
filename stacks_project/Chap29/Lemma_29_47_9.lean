/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 29.47.9: a scheme is seminormal exactly when its canonical seminormalization morphism
is an isomorphism, equivalently when every residue-field-preserving universal homeomorphism to it
from a reduced scheme is an isomorphism. -/
@[stacks 0H3G] #check
  (AlgebraicGeometry.Scheme.seminormal_iff_isIso_seminormalizationMap :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.Scheme.Seminormal X ↔
        CategoryTheory.IsIso
          ((⊥_ (AlgebraicGeometry.Scheme.SeminormalizationOver X)).1.hom))

#check
  (AlgebraicGeometry.Scheme.seminormal_iff_universalHomeomorphism_isIso :
    ∀ (X : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.Scheme.Seminormal X ↔
        ∀ {Y : AlgebraicGeometry.Scheme.{u}} (π : Y ⟶ X),
          AlgebraicGeometry.UniversalHomeomorphism π →
          (∀ y : Y, CategoryTheory.IsIso (π.residueFieldMap y)) →
          AlgebraicGeometry.IsReduced Y → CategoryTheory.IsIso π)
