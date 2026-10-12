/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
import StacksCheckRecall

/-!
# Lemma 18.24.1

The finite-presentation closure theorem for cokernels is owned at the generic
SheafOfModules.IsFinitePresentation level.
-/

@[expose] public section

open CategoryTheory Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (O : Sheaf J CommRingCat.{max u v})
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective
  AddCommGrpCat.{max u v}]
variable {G F : ringedSiteModuleCategory J O} (φ : G ⟶ F)
variable [G.IsFiniteType] [F.IsFinitePresentation]

/- Lemma 18.24.1 (0H98): the cokernel of a map from a finite-type module sheaf to a finitely
presented module sheaf is finitely presented. -/
@[stacks 0H98]
#check
  (IsFinitePresentation.cokernel φ :
    (cokernel φ).IsFinitePresentation)

end SheafOfModules
