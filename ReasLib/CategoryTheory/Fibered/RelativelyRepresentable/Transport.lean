/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.TwoFibreProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transport of representability for two-fibre products

This file bridges isomorphisms of based functors to the canonical bicategorical transport API.

An arbitrary natural isomorphism between the underlying total-category functors is deliberately
not accepted here: its components need not lie over identities in the base. The canonical
intermediate owner for such an isomorphism is `BasedFunctor`, whose morphisms record precisely
this verticality condition.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

open scoped CategoryTheory.TwoFibreProduct

/-- Representability of a two-fibre product is unchanged when both legs are replaced through
isomorphisms of their underlying based functors. The based-functor owner ensures that every
component of the comparison lies over an identity of the base. -/
@[stacks 02Y7 "transport of representability along based-functor isomorphisms"]
theorem _root_.CategoryTheory.TwoFibreProduct.IsRepresentable.congr_iff_of_basedIso
    {A B T : FiberedCategoryOver.Groupoids C}
    {F F' : A ⟶ T} {G G' : B ⟶ T}
    (α : FiberedCategoryOver.Groupoids.toBasedFunctor F ≅
      FiberedCategoryOver.Groupoids.toBasedFunctor F')
    (β : FiberedCategoryOver.Groupoids.toBasedFunctor G ≅
      FiberedCategoryOver.Groupoids.toBasedFunctor G') :
    IsRepresentable (F ⊡₂ G) ↔
      IsRepresentable (F' ⊡₂ G') := sorry
/- Proof strategy: lift `α` and `β` with
`Bicategory.InducedBicategory.isoMk`, then apply
`TwoFibreProduct.ObjectProperty.congr_iff`, specialized to
`FiberedCategoryOver.Groupoids.IsRepresentable`. -/

end FiberedCategoryOver.Groupoids

end CategoryTheory
