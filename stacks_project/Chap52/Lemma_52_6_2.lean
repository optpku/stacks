/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.GlobalSectionLocalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.RingedSiteDerived
open SheafOfModules.RingedSite.ExtendedCech

noncomputable section

universe u

open RingedSite.Hom.ModuleDerived
open RingedSite.Hom.ModuleDerived.LocalizationAway

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/- Lemma 52.6.2: for a global section `f` and `K ∈ D(O)`, vanishing of
`RHom_O(O_f, K)`, vanishing of `RHom_O(L, K)` for every `L ∈ D(O_f)`, and vanishing of
any homotopy-limit representative of the multiplication-by-`f` tower are equivalent. -/
@[stacks 0997] #check (RingedSite.Hom.ModuleDerived.LocalizationAway.vanishing_tfae :
  ∀
    (f : (unitModule J O).sections)
    (K T : max J O) (hT : HomotopyLimit.IsOf (tower f K) T),
    List.TFAE
      [ IsZero (RingedSite.Hom.ModuleDerived.InternalHom.obj (principalDerivedModule f) K),
        allInternalHomVanishing f K,
        IsZero T ])
