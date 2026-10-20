module

public import ReasLib.CategoryTheory.Fibered.AutomorphismFunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u₁ v₁ u₂ v₂

/- Definition 90.19.5: for a projection cofibered in groupoids and a supplied
cleavage of its opposite, the automorphism functor sends an arrow under `p.obj x`
to the automorphisms of its pushforward of `x` in the fibre over the codomain.
Its maps are induced by the unique compatible pushforward comparison. -/
@[stacks 06JT]
#check (CategoryTheory.Functor.Cleavage.autFunctor :
  {C : Type u₁} → [Category.{v₁} C] → {F : Type u₂} → [Category.{v₂} F] →
    {p : F ⥤ C} → [Functor.IsFibered.InGroupoids p.op] → (χ : p.op.Cleavage) →
      (x : F) → Under (p.obj x) ⥤ Type v₂)
