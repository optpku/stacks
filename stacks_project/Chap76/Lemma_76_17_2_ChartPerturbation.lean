/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Perturbation.Chart

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.Chart

variable {S : Scheme.{u}} {B X X' Y : AlgebraicSpace S}
variable {L L' W : Over S}
variable (iX : X ⟶ X') [IsFirstOrderThickening iX]
variable (iL : L ⟶ L') [AlgebraicGeometry.IsImmersion iL.left]
variable (a : X ⟶ Y) (l : L ⟶ W)
variable (qX : ofOver L ⟶ X) (qX' : ofOver L' ⟶ X') (qY : ofOver W ⟶ Y)
variable [Etale qY]
variable (sq : CommSq qX (ofOverMap l) a qY)
variable (sqI : CommSq qX (ofOverMap iL) iX qX')

variable (p : Y ⟶ B)
variable (D : Hom.derivations p ((Modules.pushforward a).obj (Hom.conormalSheaf iX)))

/- Lemma 76.17.2: The differential parameter gives the actual scheme-chart perturbation. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.Chart.perturb
    iX iL a l qX qX' qY sq sqI p D :
  ∀ {W' : Over S} (iW : W ⟶ W') (l' : L' ⟶ W')
    [AlgebraicGeometry.IsFirstOrderThickening iL.left]
    [AlgebraicGeometry.IsFirstOrderThickening iW.left]
    (sqL : CommSq l iL iW l'), L' ⟶ W')

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.Chart
