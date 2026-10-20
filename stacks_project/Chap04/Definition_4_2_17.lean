module

public import Mathlib.CategoryTheory.Equivalence
import StacksCheckRecall

@[expose] public section

universe v₁ v₂ u₁ u₂

variable (C : Type u₁) [CategoryTheory.Category.{v₁} C]
variable (D : Type u₂) [CategoryTheory.Category.{v₂} D]

/-
The source asks for a forward functor, a quasi-inverse, and natural isomorphisms for both
composites. `CategoryTheory.Equivalence` is the canonical owner of exactly this data;
`CategoryTheory.Functor.IsEquivalence` is instead the derived full, faithful, and essentially
surjective predicate on a functor. The owner's additional triangle field imposes no extra
mathematical restriction, since `CategoryTheory.Equivalence.mk` constructs it from the two source
isomorphisms without changing either functor. Recalling the bundled owner exposes its `functor`,
`inverse`, `unitIso`, and `counitIso` fields directly for downstream use.
-/

/- Definition 4.2.17: an equivalence of categories consists of a functor together with a
quasi-inverse such that both composites are naturally isomorphic to the corresponding identity
functors. -/
@[stacks 001J "equivalence of categories with a quasi-inverse"]
#check (CategoryTheory.Equivalence C D : Type max v₁ v₂ u₁ u₂)

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/-- Companion to Definition 4.2.17 (001J): a functor is an equivalence exactly when it admits a
quasi-inverse with unit and counit natural isomorphisms. -/
theorem isEquivalence_iff_exists_quasiInverse (F : A ⥤ B) :
    F.IsEquivalence ↔
      ∃ G : B ⥤ A, Nonempty (𝟭 A ≅ F ⋙ G) ∧ Nonempty (G ⋙ F ≅ 𝟭 B) := sorry

end CategoryTheory.Functor
