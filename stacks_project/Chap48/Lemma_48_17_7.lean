/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Dualizing
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.StructuredArrow
open DerivedCategory.Plus.CohomologyIn
open RingedSpace
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Scheme.Compactification
open Compactification.Of

noncomputable section

universe u

/- Lemma 48.17.7 -/
@[stacks 0AA3] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.upperShriek_isDualizingComplex :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
      (P : Of (Over.left Y.obj) (Over.mk (Over.Hom.left f.hom)))
      (a : DerivedQCoh (Over.left Y.obj) ⥤ DerivedQCoh (Over.left (right P.obj)))
      (aAdjunction : DerivedQCoh.pushforwardCohomologyIn (Over.hom (right P.obj)) ⊣ a)
      (aPlus : DerivedQCoh.Plus (Over.left Y.obj) ⥤
        DerivedQCoh.Plus (Over.left (right P.obj)))
      (aPlusCompatibility :
        aPlus ⋙ ambient (quasiCoherentModuleProperty (Over.left (right P.obj))) ≅
          toUnbounded (quasiCoherentModuleProperty (Over.left Y.obj)) ⋙
            a ⋙ DerivedQCoh.inclusion (Over.left (right P.obj)))
      (K : DerivedQCoh.Plus (Over.left Y.obj))
      (hK : IsDualizingComplex K.obj.obj),
      IsDualizingComplex ((upperShriek f P aPlus).obj K).obj.obj)
