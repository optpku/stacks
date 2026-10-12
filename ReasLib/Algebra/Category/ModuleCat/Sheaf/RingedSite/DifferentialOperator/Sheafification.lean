/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DifferentialOperator
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationBaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential operators and module sheafification

Module sheafification preserves an objectwise differential-operator order bound.
The statement is formulated for `mapAfterRestriction`, so it simultaneously
handles the change of coefficient ring needed by relative constructions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ModuleSheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O O' : Sheaf J CommRingCat.{max u v}}
variable (b : O ⟶ O')
variable {P Q : PresheafOfModules (ringSheaf J O').obj}

/-- Sheafifying a presheaf differential operator after restriction of scalars
preserves its order bound. -/
@[stacks 0G3Y "sheafification preserves differential-operator order"]
theorem mapAfterRestriction_isOrderLE
    (f : (PresheafOfModules.restrictScalars (ringSheafMap b).hom).obj P ⟶
      (PresheafOfModules.restrictScalars (ringSheafMap b).hom).obj Q)
    {k : ℕ} (hf : PresheafOfModules.IsDifferentialOperatorOfOrder b.hom f k) :
    IsDifferentialOperatorOfOrder b (mapAfterRestriction b f) k := sorry

end SheafOfModules.RingedSite.ModuleSheafification

namespace PresheafOfModules.ModuleSheafification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}} (phi : O₁ ⟶ O₂)
variable {F G : PresheafOfModules (ringPresheaf O₂)}

/-- Canonical commutative-ring module sheafification preserves an objectwise
differential-operator order bound, including the required change of coefficient ring. -/
@[stacks 0G3Y "commutative-ring module sheafification preserves operator order"]
theorem mapAfterRestriction_isOrderLE
    (f : (PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap phi)).obj F ⟶
      (PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap phi)).obj G)
    {k : ℕ} (hf : PresheafOfModules.IsDifferentialOperatorOfOrder phi f k) :
    SheafOfModules.RingedSite.IsDifferentialOperatorOfOrder
      (PresheafOfModules.commRingSheafificationMap J phi)
      (mapAfterRestriction J phi f) k := sorry

end PresheafOfModules.ModuleSheafification
