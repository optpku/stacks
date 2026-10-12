/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

variable {C : Type u} [Category.{u} C]
variable {𝒪₁ 𝒪₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (α : 𝒪₁ ⟶ 𝒪₂)
variable (G : PresheafOfModules (ringPresheaf 𝒪₁))
variable (F : PresheafOfModules (ringPresheaf 𝒪₂))

/- Lemma 18.9.2 (03CU): morphisms from `G` to `F` with scalars restricted along `α`
correspond canonically to morphisms from the extension of `G` to `F`. -/
@[stacks 03CU]
#check
  (PresheafOfModules.ChangeOfRings.restrictionExtensionHomEquiv
    (PresheafOfModules.presheafStructureMap α) G F)
