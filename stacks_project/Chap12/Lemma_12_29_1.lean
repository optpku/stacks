module

public import ReasLib.CategoryTheory.Adjunction.Abelian
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 12.29.1 compatibility facade

The reusable adjunction/exactness API is owned by
`ReasLib.CategoryTheory.Adjunction.Abelian`. This module retains the historical Chapter 12
import path.
-/

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {L : A ⥤ B} {R : B ⥤ A} [R.Additive]

variable (adj : R ⊣ L)

/- Lemma 12.29.1 (1) [015Z]: an additive left adjoint preserves monomorphisms exactly when it is
exact. -/
@[stacks 015Z "(1)"]
#check (Adjunction.LeftAdjoint.preservesMonomorphisms_iff_exact adj :
  R.PreservesMonomorphisms ↔ exactFunctor B A R)

variable {A₀ : Type u₁} [Category.{v₁} A₀]
variable {B₀ : Type u₂} [Category.{v₂} B₀]
variable {L₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀}
variable (adj₀ : R₀ ⊣ L₀) (h_exact : exactFunctor B₀ A₀ R₀)

/- Lemma 12.29.1 (2) [015Z]: an exact left adjoint sends injectives through its right adjoint. -/
@[stacks 015Z "(2)"]
#check (Adjunction.RightAdjoint.preservesInjectiveObjects_of_leftExact adj₀ h_exact :
  L₀.PreservesInjectiveObjects)

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [EnoughInjectives D]
variable {F : C ⥤ D} {G : D ⥤ C} [G.PreservesInjectiveObjects]
variable (adj₁ : F ⊣ G)

/- Lemma 12.29.1 (3) is the canonical mathlib adjunction criterion. -/
@[stacks 015Z "(3)"]
#check (Functor.preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects adj₁ :
  F.PreservesMonomorphisms)

end CategoryTheory
