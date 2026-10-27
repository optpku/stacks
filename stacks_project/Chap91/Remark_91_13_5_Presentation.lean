/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.AlgebraExtension.Presentation

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite
open scoped CategoryTheory.Sheaf.FreeAlgebra

noncomputable section

universe c v w

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O_B O : Sheaf J CommRingCat.{w}}
variable {fSharp : O_B ⟶ O}
variable {G : SheafOfModules (ringSheaf J O)}

variable [HasSheafify J AddCommGrpCat.{w}]

/- The lifted generators induce a map from the presentation conormal module to the kernel. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.Solution.conormalHom :
  (S : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp G (zeroKernelMap fSharp G)) →
  (E : Sheaf J (Type w)) → (α' : E ⟶ (sheafForget J).obj S.middle) →
  (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk fSharp)) →
  assignOf S E α' = α → ((Presentation.ofGenerators E α).X (-1) ⟶ G))
