/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.43.13 (1): over a quasi-compact and quasi-separated base, a morphism is
projective if and only if it is quasi-projective and proper. -/
@[stacks 0BCL] #check
  (AlgebraicGeometry.projective_iff_quasiProjective_and_isProper :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [CompactSpace S] [QuasiSeparatedSpace S],
      AlgebraicGeometry.Projective f ↔
        AlgebraicGeometry.QuasiProjective f ∧ AlgebraicGeometry.IsProper f)

/- Lemma 29.43.13 (2): over a quasi-compact and quasi-separated base, a morphism is
H-projective if and only if it is H-quasi-projective and proper. -/
@[stacks 0BCL] #check
  (AlgebraicGeometry.hProjective_iff_hQuasiProjective_and_isProper :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [CompactSpace S] [QuasiSeparatedSpace S],
      AlgebraicGeometry.HProjective f ↔
        AlgebraicGeometry.HQuasiProjective f ∧ AlgebraicGeometry.IsProper f)
