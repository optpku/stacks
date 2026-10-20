module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import StacksCheckRecall

/-!
# Lemma 18.11.2

Exactness is exposed through Mathlib's bundled exact-functor owner for module sheafification.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe z w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J RingCat.{w}]
variable [J.WEqualsLocallyBijective RingCat.{w}]
variable [HasSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable (𝒪 : Cᵒᵖ ⥤ RingCat.{w})

/- Lemma 18.11.2 (03EI): sheafification of module presheaves along the canonical
ring-sheafification map is an exact functor. -/
@[stacks 03EI]
#check
  (ExactFunctor.of
      (PresheafOfModules.sheafification (CategoryTheory.toSheafify J 𝒪)) :
    PresheafOfModules.{z} 𝒪 ⥤ₑ
      SheafOfModules.{z} ((presheafToSheaf J RingCat.{w}).obj 𝒪))
