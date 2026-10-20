/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalProjectiveBundle
import ReasLib.AlgebraicGeometry.Scheme.Blowup.SmoothCenter

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 37.17.3 (1): if a scheme and a closed center are smooth over the same base, then the
blowup in that center is smooth over the base. -/
@[stacks 0FUT] #check
  (AlgebraicGeometry.IsBlowup.smooth_of_smooth_center :
    ∀ {S X X' : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
      [Smooth f] [Smooth (I.subschemeι ≫ f)] [AlgebraicGeometry.IsBlowup b I],
      Smooth (b ≫ f))

/- Lemma 37.17.3 (2): under the same hypotheses, the exceptional divisor is smooth over the
base. -/
@[stacks 0FUT] #check
  (AlgebraicGeometry.IsBlowup.exceptionalDivisor_smooth_of_smooth_center :
    ∀ {S X X' : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
      [Smooth f] [Smooth (I.subschemeι ≫ f)] [AlgebraicGeometry.IsBlowup b I],
      Smooth ((I.comap b).subschemeι ≫ b ≫ f))

/- Lemma 37.17.3 (3): the canonical map from the exceptional divisor to any chosen model of
the projective bundle of the center's conormal sheaf is an isomorphism. -/
@[stacks 0FUT] #check
  (AlgebraicGeometry.IsBlowup.exceptionalProjectiveComparison_isIso_of_smooth :
    ∀ {S X X' P : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
      [Smooth f] [Smooth (I.subschemeι ≫ f)] [AlgebraicGeometry.IsBlowup b I]
      (q : P ⟶ I.subscheme)
      (hP : Scheme.ProjectiveBundle.Representation q
        (Scheme.Hom.conormalSheaf I.subschemeι)),
      IsIso (AlgebraicGeometry.IsBlowup.exceptionalProjectiveComparison I b q hP))

/- The canonical comparison respects the projections to the center. -/
#check
  (AlgebraicGeometry.IsBlowup.exceptionalProjectiveComparison_over :
    ∀ {X X' P : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
      [AlgebraicGeometry.IsBlowup b I] (q : P ⟶ I.subscheme)
      (hP : Scheme.ProjectiveBundle.Representation q
        (Scheme.Hom.conormalSheaf I.subschemeι)),
      AlgebraicGeometry.IsBlowup.exceptionalProjectiveComparison I b q hP ≫ q =
        AlgebraicGeometry.IsBlowup.exceptionalProjection I b)

/- Lemma 37.17.3 (4): under the same hypotheses, the pullback of the projective bundle's
tautological sheaf is canonically isomorphic to the restriction of `𝒪o_{X'}(-E)` to the
exceptional divisor. -/
@[stacks 0FUT] #check
  (AlgebraicGeometry.IsBlowup.exceptionalTautologicalIso_of_smooth :
    ∀ {S X X' P : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (b : X' ⟶ X)
      [Smooth f] [Smooth (I.subschemeι ≫ f)] [AlgebraicGeometry.IsBlowup b I]
      (q : P ⟶ I.subscheme)
      (hP : Scheme.ProjectiveBundle.Representation q
        (Scheme.Hom.conormalSheaf I.subschemeι)),
      (Scheme.Modules.pullback
          (AlgebraicGeometry.IsBlowup.exceptionalProjectiveComparison I b q hP)).obj
          (Scheme.ProjectiveBundle.tautologicalSheaf q hP) ≅
      (Scheme.Modules.pullback (I.comap b).subschemeι).obj (I.comap b).negSheaf)
