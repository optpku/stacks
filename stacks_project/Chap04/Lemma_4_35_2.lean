module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Pseudofunctor

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Lemma 4.35.2 (1): a functor is fibred in groupoids exactly when it is fibred and every
standard fibre is a groupoid. -/
@[stacks 003V "(1)"]
#check (Functor.IsFibered.InGroupoids.iff_isFibered_fibersGroupoid :
  (p : S ⥤ C) →
    Functor.IsFibered.InGroupoids p ↔
      p.IsFibered ∧ ∀ U : C, IsGroupoid (p.Fiber U))

/- Lemma 4.35.2 (2): every total morphism of a category fibred in groupoids is strongly
cartesian over its image. -/
@[stacks 003V "(2)"]
#check (Functor.IsFibered.InGroupoids.all_isStronglyCartesian :
  {p : S ⥤ C} → [Functor.IsFibered.InGroupoids p] →
    {x y : S} → (φ : x ⟶ y) → p.IsStronglyCartesian (p.map φ) φ)

/- Lemma 4.35.2 (3): the canonical fibre pseudofunctor of a chosen cleavage on a category fibred
in groupoids is groupoid-valued. -/
@[stacks 003V "(3)"]
#check (fun {p : S ⥤ C} [Functor.IsFibered.InGroupoids p]
    (χ : p.Cleavage) ↦
  Functor.Cleavage.toPseudofunctor.isGroupoidValued χ :
  ∀ {p : S ⥤ C} [Functor.IsFibered.InGroupoids p] (χ : p.Cleavage),
    ∀ U : LocallyDiscrete Cᵒᵖ, IsGroupoid ((χ.toPseudofunctor).obj U))

end CategoryTheory
