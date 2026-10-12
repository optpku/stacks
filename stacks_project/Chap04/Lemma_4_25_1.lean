/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Corepresentable
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u uI

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{v, v, v, u} C]
variable (F : C ⥤ Type w) [PreservesLimitsOfSize.{v, v} F]
variable {I : Type uI} [Small.{v} I]
variable (X : I → C) (x : ∀ i : I, F.obj (X i))
variable (h_generate : ∀ ⦃Y : C⦄ (g : F.obj Y),
  ∃ i : I, ∃ phi : X i ⟶ Y, F.map phi (x i) = g)

/- Lemma 4.25.1: a limit-preserving type-valued functor with a small jointly generating family
of elements is corepresentable. -/
@[stacks 0AHN]
#check (isCorepresentable_of_preservesLimits_of_generating_family F X x h_generate :
  F.IsCorepresentable)

/- The construction factors through the reusable initial-element criterion. -/
#check CategoryTheory.Functor.isCorepresentable_of_hasInitial_elements

end CategoryTheory.Functor
