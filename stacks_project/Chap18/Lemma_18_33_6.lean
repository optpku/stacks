/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.Localization
import StacksCheckRecall

/-!
# Lemma 18.33.6 compatibility entry point

Localization of relative differentials is owned by the generic slice-site API
in ReasLib.
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
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C,
  (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable (phi : O₁ ⟶ O₂) (U : C)

/- Lemma 18.33.6 (04BO): restricting `Ω(phi)` to the slice site over
`U` agrees with the relative differentials of the restricted ring map. -/
@[stacks 04BO]
#check (over_isIsomorphic phi U :
  IsIsomorphic
    ((SheafOfModules.toSheaf ((ringSheaf J O₂).over U)).obj
      ((relativeDifferentials phi).over U))
    ((SheafOfModules.toSheaf
      (ringSheaf (J.over U) (O₂.over U))).obj (localized phi U)))

/- The localized ring morphism is exposed independently for downstream
specialization. -/
#check (localizedMap phi U : O₁.over U ⟶ O₂.over U)

end SheafOfModules.RingedSite.RelativeDifferentials
