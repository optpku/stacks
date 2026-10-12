/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.BaseChange
import StacksCheckRecall

/-!
# Lemma 18.33.7 compatibility entry point

Functoriality of relative differentials under commutative ring squares is
owned by the generic ReasLib base-change API.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.RelativeDifferentials

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {phi : O₁ ⟶ O₂}
variable {phi' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}
variable (sq : CommSq a phi phi' b)

/- Lemma 18.33.7 (08TR): a commutative square of commutative ring
sheaves induces the canonical map on relative differentials. -/
@[stacks 08TR]
#check (map sq :
  relativeDifferentials phi ⟶
    (restrictionAlong b).obj (relativeDifferentials phi'))

/- The owner includes the generator formula and uniqueness characterization. -/
#check map_d sq
#check map_unique sq
#check map_comp

end SheafOfModules.RingedSite.RelativeDifferentials
