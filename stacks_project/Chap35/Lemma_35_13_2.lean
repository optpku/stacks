/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineScheme.SectionDescent
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 35.13.2: a family of morphisms of affine schemes has quasicoherent section descent
if and only if it is a universal effective epimorphic family. -/
@[stacks 0EUA]
#check
  (AlgebraicGeometry.AffineScheme.hasQuasicoherentSectionDescent_iff_universalEffectiveEpi :
    ∀ (X : AlgebraicGeometry.AffineScheme.{u})
      (K : CategoryTheory.SemiRepresentableFamily.Over.{v} X),
      AlgebraicGeometry.AffineScheme.HasQuasicoherentSectionDescent X K ↔
        CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily K)
