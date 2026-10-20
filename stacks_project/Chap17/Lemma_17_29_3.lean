/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Construction
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)

/- Lemma 17.29.3 (0G3S): order-bounded differential operators from a fixed module sheaf are
corepresentable by a sheaf of principal parts. -/
@[stacks 0G3S]
#check
  (DifferentialOperators.isCorepresentable φ F k :
    (DifferentialOperators.functor φ F k).IsCorepresentable)

#check @PrincipalParts.representsDifferentialOperators
#check @PrincipalParts.toHom_homEquiv
#check @PrincipalParts.homEquiv_symm_apply
#check @PrincipalParts.representingIso_hom_app
#check @PrincipalParts.representingIso_inv_app

/- The bounded differential-operator API is functorial in the source as well as the target. -/
#check @DifferentialOperators.sourceMap
#check @DifferentialOperators.sourceGroupFunctor
#check @DifferentialOperators.sourceFunctor
#check @DifferentialOperators.bimap
#check @DifferentialOperators.groupBifunctor
#check @DifferentialOperators.bifunctor

end SheafOfModules.RingedSite
