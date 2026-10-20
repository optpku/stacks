/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Differentials
import StacksCheckRecall

/-!
# Lemma 18.33.11 compatibility entry point

The canonical pullback comparison for relative differentials, its universal characterization,
and its uniqueness API are owned by
`ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Differentials`.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom.Differentials

variable {CX CX' CY CY' : Type u}
variable [Category.{u} CX] [Category.{u} CX'] [Category.{u} CY] [Category.{u} CY']
variable {JX : GrothendieckTopology CX} {JX' : GrothendieckTopology CX'}
variable {JY : GrothendieckTopology CY} {JY' : GrothendieckTopology CY'}
variable [JX.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JX'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JY.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JY'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JX CommRingCat.{u}]
variable [HasWeakSheafify JX AddCommGrpCat.{u}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JX' CommRingCat.{u}]
variable [HasWeakSheafify JX' AddCommGrpCat.{u}]
variable [JX'.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OX : Sheaf JX CommRingCat.{u}} {OX' : Sheaf JX' CommRingCat.{u}}
variable {OY : Sheaf JY CommRingCat.{u}} {OY' : Sheaf JY' CommRingCat.{u}}

variable
  (f : RingedSite.Hom
    (RingedSite.ofCommRingSheaf JX' OX') (RingedSite.ofCommRingSheaf JX OX))
  (g : RingedSite.Hom
    (RingedSite.ofCommRingSheaf JY' OY') (RingedSite.ofCommRingSheaf JY OY))
  (h : RingedSite.Hom
    (RingedSite.ofCommRingSheaf JX OX) (RingedSite.ofCommRingSheaf JY OY))
  (h' : RingedSite.Hom
    (RingedSite.ofCommRingSheaf JX' OX') (RingedSite.ofCommRingSheaf JY' OY'))
  (sq : Commutes f g h h')

/- Lemma 18.33.11 (04BR): a commutative square of morphisms of ringed topoi has a unique
comparison from the pullback of the relative-differentials sheaf on `X` over `Y` to that on
`X'` over `Y'`, characterized by carrying universal differentials to the differentials of pulled
sections after adjunction. -/
@[stacks 04BR]
#check (existsUnique_comparison f g h h' sq :
  ∃! tau : (SheafOfModules.pullback f.structureSheafMap).obj
      (relativeDifferentials (inverseImageStructureSheafMap h)) ⟶
    relativeDifferentials (inverseImageStructureSheafMap h'),
    IsComparison f h h' tau)

/- The reusable owner supplies the canonical comparison as concrete data. -/
#check (comparison f g h h' sq :
  (SheafOfModules.pullback f.structureSheafMap).obj
      (relativeDifferentials (inverseImageStructureSheafMap h)) ⟶
    relativeDifferentials (inverseImageStructureSheafMap h'))

/- Its source-facing characterization is available independently of the chosen square proof. -/
#check (comparison_isComparison f g h h' sq :
  IsComparison f h h' (comparison f g h h' sq))

/- The raw data-safe square relation is equivalent to Mathlib's bundled `CommSq`. -/
#check commutes_iff_commSq f g h h'

end RingedSite.Hom.Differentials
