/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.GabrielPopescu.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.Derived

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
variable [HasDerivedCategory C]

/- Lemma 19.14.4 (1): the canonical exact Gabriel-Popescu functor and its K-injective
right derived functor form an adjunction on derived categories. -/
@[stacks 0F5V] #check
  (adjunction C : left C ⊣ right C)

/- Lemma 19.14.4 (2): the counit `right C ⋙ left C ⟶ 𝟭 (DerivedCategory C)` is an
isomorphism, expressing `left C ∘ right C ≅ 𝟭`. -/
@[stacks 0F5V] #check
  (counitIsIso C : IsIso (adjunction C).counit)

/- Lemma 19.14.4 (3): the right derived Gabriel-Popescu embedding is full. -/
@[stacks 0F5V] #check
  (rightFull C : (right C).Full)

/- Lemma 19.14.4 (4): the right derived Gabriel-Popescu embedding is faithful. -/
@[stacks 0F5V] #check
  (rightFaithful C : (right C).Faithful)

end CategoryTheory.IsGrothendieckAbelian.GabrielPopescu.Derived
