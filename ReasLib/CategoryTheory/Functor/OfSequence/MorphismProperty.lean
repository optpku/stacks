/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphism properties along sequential diagrams

This file promotes a property of every successor map in a sequential diagram to every map in
the diagram. The property is assumed to contain identities and be closed under composition.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

namespace OfSequence

/-- Every map in a sequential diagram belongs to a multiplicative morphism property when all
successor maps do. -/
@[stacks 0193 "multiplicative morphism property along a sequence"]
theorem map_mem (F : ℕ ⥤ C) (W : MorphismProperty C) [W.IsMultiplicative]
    (hF : ∀ n : ℕ, W (F.map (homOfLE (Nat.le_succ n))))
    {i j : ℕ} (f : i ⟶ j) : W (F.map f) := sorry

/-- If every successor map in a sequential diagram is monic, then every map is monic. -/
@[stacks 0193 "monomorphisms along a sequence"]
theorem map_mono (F : ℕ ⥤ C)
    (hF : ∀ n : ℕ, Mono (F.map (homOfLE (Nat.le_succ n))))
    {i j : ℕ} (f : i ⟶ j) : Mono (F.map f) := sorry

/-- If every successor map in a sequential diagram is epic, then every map is epic. -/
@[stacks 0193 "epimorphisms along a sequence"]
theorem map_epi (F : ℕ ⥤ C)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n))))
    {i j : ℕ} (f : i ⟶ j) : Epi (F.map f) := sorry

end OfSequence

namespace OfOpSequence

/-- Every map in an inverse sequential diagram belongs to a multiplicative morphism property
when all predecessor maps do. -/
@[stacks 0193 "multiplicative morphism property along an inverse sequence"]
theorem map_mem (F : ℕᵒᵖ ⥤ C) (W : MorphismProperty C) [W.IsMultiplicative]
    (hF : ∀ n : ℕ, W (F.map (homOfLE (Nat.le_succ n)).op))
    {i j : ℕᵒᵖ} (f : i ⟶ j) : W (F.map f) := sorry

/-- If every predecessor map in an inverse sequential diagram is monic, then every map is
monic. -/
@[stacks 0193 "monomorphisms along an inverse sequence"]
theorem map_mono (F : ℕᵒᵖ ⥤ C)
    (hF : ∀ n : ℕ, Mono (F.map (homOfLE (Nat.le_succ n)).op))
    {i j : ℕᵒᵖ} (f : i ⟶ j) : Mono (F.map f) := sorry

/-- If every predecessor map in an inverse sequential diagram is epic, then every map is
epic. -/
@[stacks 0193 "epimorphisms along an inverse sequence"]
theorem map_epi (F : ℕᵒᵖ ⥤ C)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    {i j : ℕᵒᵖ} (f : i ⟶ j) : Epi (F.map f) := sorry

end OfOpSequence

end CategoryTheory.Functor
