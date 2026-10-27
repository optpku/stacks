/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Solution

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable {O_B' O_B O : Sheaf J CommRingCat.{w}}
variable (π : O_B' ⟶ O_B) [Sheaf.IsLocallySurjective π]

variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (hπ : KernelIdeal.IsSquareZero π)
variable (fSharp : O_B ⟶ O)
variable (G : SheafOfModules (ringSheaf J O))
variable (c :
    hπ.targetModule (KernelIdeal.quotientComparison_isIso π) ⟶
      (restrictionAlong fSharp).obj G)

/- 91.13.0.1 A solution fills the fixed first-order extension diagram and induces c on kernels. -/
#check (Solution π hπ fSharp G c : Type _)

#check (Solution.ofMaps π hπ fSharp G c :
  ∀ (middle : Sheaf J CommRingCat.{w}) (proj : middle ⟶ O)
    (structureMap : O_B' ⟶ middle)
    (hs : Sheaf.IsLocallySurjective proj) (hz : KernelIdeal.IsSquareZero proj)
    (hi : IsIso (KernelIdeal.quotientComparison proj))
    (hc : structureMap ≫ proj = π ≫ fSharp)
    (e : hz.targetModule hi ≅ G),
    kernelMapOf π hπ fSharp proj hz hi structureMap hc ≫
      (restrictionAlong fSharp).map e.hom = c → Solution π hπ fSharp G c)

end SheafOfModules.RingedSite.FirstOrderThickening
