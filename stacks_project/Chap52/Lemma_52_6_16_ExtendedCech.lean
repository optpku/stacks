/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExtendedCech

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite.ExtendedCech

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O O' : Sheaf J CommRingCat.{u}} {r : ℕ}

/- The canonical comparison of extended alternating Čech complexes. -/
#check (SheafOfModules.RingedSite.ExtendedCech.map :
  ∀ (alpha : O ⟶ O') (f : Fin r → (unitModule J O).sections),
    complex f ⟶ targetComplex alpha f)

end SheafOfModules.RingedSite.ExtendedCech
