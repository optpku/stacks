/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.AlmostBlowup.Tests
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 38.37.12: a type-valued presheaf on a chosen big h-site slice is an
h-sheaf if and only if it satisfies Zariski descent, affine-target equalizer
descent for surjective flat proper morphisms of finite presentation, descent
for nilpotent principal-center quotient squares, and descent for two-generator
projective almost-blowup squares. -/
@[stacks 0EVI] #check
  (AlgebraicGeometry.ChosenBigHSite.Sheaf.iffZariskiAndFlatProperExampleDescent :
    ∀ (Schh : AlgebraicGeometry.ChosenBigHSite.{u, v}) (S : Schh.carrier)
        (F : (Over S)ᵒᵖ ⥤ Type (max u v)),
      Presheaf.IsSheaf (AlgebraicGeometry.ChosenBigHSite.bigTopology Schh S) F ↔
        Presheaf.IsSheaf
            (AlgebraicGeometry.ChosenBigHSite.bigZariskiTopology Schh S) F ∧
          AlgebraicGeometry.ChosenBigHSite.Equalizer.IsAffineFlatProperSurjective
              Schh S F ∧
            AlgebraicGeometry.AlmostBlowupDescent.IsPrincipalCenter
                (AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S) F ∧
              AlgebraicGeometry.AlmostBlowupDescent.IsTwoGenerator
                (AlgebraicGeometry.ChosenBigSite.sliceToScheme Schh S) F)
