/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
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

/- Lemma 52.6.16: a flat morphism inducing an isomorphism on the quotients by a finite
family of global sections induces a quasi-isomorphism of extended alternating Čech complexes. -/
@[stacks 099H] #check (SheafOfModules.RingedSite.ExtendedCech.map_quasiIso :
  ∀ (alpha : O ⟶ O') (h_flat : IsFlatHom alpha)
    (f : Fin r → (unitModule J O).sections)
    [IsIso (IdealSheaf.TargetQuotient.ringMap alpha (generatedIdeal f))],
    QuasiIso (map alpha f))

end SheafOfModules.RingedSite.ExtendedCech
