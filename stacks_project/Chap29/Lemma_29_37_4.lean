/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Characterization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.37.4: for a quasi-compact morphism and an invertible module on its source, relative
ampleness, its open-local and affine-local forms, and the three relative projective section-map
criteria are equivalent. -/
@[stacks 01VJ] #check
  (AlgebraicGeometry.relativelyAmple_tfae :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
      [QuasiCompact f] [Scheme.Modules.Invertible L],
      List.TFAE [
        RelativelyAmple f L,
        RelativelyAmpleOnBaseOpenCover f L,
        AmpleOnAffineBaseOpenCover f L,
        HasRelativeProjSectionMap f L @IsOpenImmersion,
        HasCanonicalOpenImmersionRelativeProjSectionMap f L,
        HasRelativeProjSectionMap f L @IsImmersion])
