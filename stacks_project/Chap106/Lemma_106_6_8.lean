/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Lift.FirstOrderBand
import StacksCheckRecall

/-!
# Automorphism sheaves of first-order lifts are abelian and quasi-coherent

In the gerbe of lifts along a first-order thickening, automorphism sheaves of
objects are abelian, and the band of Lemma 8.11.8 is a quasi-coherent
`O_W`-module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open Functor.IsFibered.InGroupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

/- Lemma 106.6.8 (1): in the gerbe of lifts `p : C ⥤ W_spaces,étale` of
Remark 106.6.1, if `X ⊂ X'` is a first-order thickening, then the
automorphism sheaves of objects are abelian. -/
@[stacks 0CKG] #check
  (AlgebraicGeometry.AlgebraicStack.Lift.instAutomorphismIsAbelian :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
      {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x]
      [IsFirstOrderThickening iX], Automorphism.IsAbelian (p iX x))

/- Lemma 106.6.8 (2): the sheaf of groups `G` constructed in Lemma 8.11.8 is a
quasi-coherent `O_W`-module. -/
@[stacks 0CKG] #check
  (AlgebraicGeometry.AlgebraicStack.Lift.exists_quasicoherentBandModule :
    ∀ {S : Scheme.{u}} {X X' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] (iX : X ⟶ X') [IsThickening iX]
      {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X) [Groupoids.Hom.Smooth x]
      [IsFirstOrderThickening iX]
      (G : Sheaf (AlgebraicSpace.spacesEtaleTopology W) AddCommGrpCat.{u + 1})
      (hG : IsBand (p iX x) (AlgebraicSpace.spacesEtaleTopology W) G),
      ∃ M : RingedSite.ModuleCat.{u + 1} (AlgebraicSpace.commRingedSiteLift W),
        M.IsQuasicoherent ∧
          Nonempty ((AlgebraicSpace.GerbeModuleDescent.additiveExtension W).obj
            ((SheafOfModules.toSheaf (AlgebraicSpace.commRingedSiteLift W).structureSheaf).obj M)
              ≅ G))

end AlgebraicGeometry.AlgebraicStack.Lift
