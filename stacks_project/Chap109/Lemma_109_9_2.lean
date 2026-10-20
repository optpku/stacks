/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.H0Dim1
import StacksCheckRecall

/-!
# The h0,1 locus of curves is contained in the CM,1 locus

As open substacks of 𝒞urves, 𝒞urves^{h0, 1} is contained in 𝒞urves^{CM, 1}.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Lemma 109.9.2: we have 𝒞urves^{h0, 1} ⊂ 𝒞urves^{CM, 1} as open substacks of 𝒞urves. -/
@[stacks 0E6J]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.h0Dim1_le_cohenMacaulayDim1 :
  ∀ S : Scheme.{u},
    h0Dim1 S ≤ fun P ↦
      (∀ x : Points (space P),
          FlatAt (hom P) x ∧
            existsEtaleSquareAt Scheme.Germ.MorphismProperty.fiberStalkCohenMacaulay
              (hom P) x) ∧
        RelativeDimension (hom P) 1)
