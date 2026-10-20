/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.StructureSheafFlatBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.Hom

noncomputable section

universe u

/- Lemma 37.72.6 (1): in a commutative triangle `X ⟶ Y ⟶ S`, if `X` is flat
over `S`, `f : X ⟶ Y` is proper with fibres of dimension at most one, and
`R¹f_*𝒪_X = 0`, then `f_*𝒪_X` is flat over `S`. -/
@[stacks 0E7K] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.pushforwardStructureSheaf_isFlatOver :
    ∀ {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)
      (sq : CommSq f p q (𝟙 S)) [Flat p] [IsProper f]
      (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
      (hR1 : IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom
        (SheafOfModules.unit X.ringCatSheaf) 1)),
      SheafOfModules.IsFlatOver
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
        q.toShHom)

/- Lemma 37.72.6 (2): under the same hypotheses, formation of `f_*𝒪_X`
commutes with every base change `S' ⟶ S`: for any chosen cartesian presentations
of `Y' = Y ×_S S'` and `X' = X ×_Y Y'`, the canonical base-change component is
invertible. -/
@[stacks 0E7K] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.pushforwardStructureSheaf_baseChange_isIso :
    ∀ {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)
      (sq : CommSq f p q (𝟙 S)) [Flat p] [IsProper f]
      (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
      (hR1 : IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom
        (SheafOfModules.unit X.ringCatSheaf) 1))
      {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
      (gY : Y' ⟶ Y) (q' : Y' ⟶ S') (hY : IsPullback gY q' q g)
      (gX : X' ⟶ X) (f' : X' ⟶ Y') (hf : IsPullback gX f' f gY),
      IsIso ((BaseChange.map
        ((hf.toCommSq.map (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace)) :
            CommSq gX.toShHom f'.toShHom f.toShHom gY.toShHom)).app
              (SheafOfModules.unit X.ringCatSheaf)))
