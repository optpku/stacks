/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Thickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.IsFirstOrderThickening

variable {X X' : Scheme.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]
variable [hWeakSheafify : HasWeakSheafify
  (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
variable [hLocallyBijective :
  (Opens.grothendieckTopology X.toTopCat).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [hExt : HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
variable [hExt' : HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X'.toTopCat) AddCommGrpCat.{u})]
variable [hSheafify : HasSheafify
  (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
variable [hSheafify' : HasSheafify
  (Opens.grothendieckTopology X'.toTopCat) AddCommGrpCat.{u}]
variable [hCommRingToRing :
  (Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (forget₂ CommRingCat.{u} RingCat.{u})]
variable [hRingToAddCommGrp :
  (Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [hForgetCommRing :
  (Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [hTypeSheafify : HasWeakSheafify
  (Opens.grothendieckTopology X.toTopCat) (Type u)]
variable [hXLocallyRinged : Sheaf.IsLocallyRinged X.sheaf]

/- Lemma 37.4.1: a first-order thickening `i : X ⟶ X'` has the canonical
exact sequence
`0 ⟶ H⁰(X, 𝓘) ⟶ H⁰(X', 𝒪_X'ˣ) ⟶ H⁰(X, 𝒪_Xˣ) ⟶ H¹(X, 𝓘) ⟶
  Pic(X') ⟶ Pic(X) ⟶ H²(X, 𝓘) ⟶ ⋯`,
where `𝓘` is the square-zero ideal sheaf of the thickening. -/
@[stacks 0C6R] #check
  (AlgebraicGeometry.IsFirstOrderThickening.picardCohomologySequence_exact i :
    (AlgebraicGeometry.IsFirstOrderThickening.picardCohomologySequence i).Exact)

end AlgebraicGeometry.IsFirstOrderThickening
