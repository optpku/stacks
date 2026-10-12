/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import StacksCheckRecall

/-!
# Lemma 18.11.1

Module sheafification and its universal factorization are owned by Mathlib's canonical
sheafification adjunction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe z w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J RingCat.{w}]
variable [J.WEqualsLocallyBijective RingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{w})

/- Lemma 18.11.1 (03CY): sheafifying module presheaves along the ring-sheafification unit is
left adjoint to forgetting the sheaf condition and restricting scalars. This adjunction packages
the canonical module structure on the additive sheafification and its unique factorization
property. -/
@[stacks 03CY]
#check
  (PresheafOfModules.sheafificationAdjunction (CategoryTheory.toSheafify J 𝒪) :
    PresheafOfModules.sheafification (CategoryTheory.toSheafify J 𝒪) ⊣
      SheafOfModules.forget ((presheafToSheaf J RingCat.{w}).obj 𝒪) ⋙
        PresheafOfModules.restrictScalars (CategoryTheory.toSheafify J 𝒪))

/- Forgetting the module structure identifies module sheafification with additive
sheafification. -/
#check PresheafOfModules.sheafificationCompToSheaf (CategoryTheory.toSheafify J 𝒪)

variable (ℱ : PresheafOfModules.{z} 𝒪)

/- The unit of module sheafification is the additive sheafification map after forgetting the
module structure. -/
#check
  (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
    (CategoryTheory.toSheafify J 𝒪) ℱ)
