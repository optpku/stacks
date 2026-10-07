module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# The category of split truncated simplicial objects

This module bundles a chosen truncated splitting and defines morphisms preserving its
distinguished summands.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable (C : Type u) [Category.{v} C] (n : ℕ)

/-- A truncated simplicial object equipped with a chosen splitting. -/
@[ext, stacks 017P "split truncated simplicial object"]
structure Split where
  /-- The underlying truncated simplicial object. -/
  X : SimplicialObject.Truncated C n
  /-- The chosen splitting of the underlying truncated simplicial object. -/
  s : Splitting X

namespace Split

variable {C : Type u} [Category.{v} C] {n : ℕ}

/-- Bundle a chosen splitting as a split truncated simplicial object. -/
@[stacks 017P "bundle a split truncated simplicial object"]
def mk' {X : SimplicialObject.Truncated C n} (s : Splitting X) : Split C n :=
  ⟨X, s⟩

/-- A morphism of split truncated simplicial objects consists of an underlying morphism and
compatible maps between all distinguished summands. -/
@[stacks 017P "morphism of split truncated simplicial objects"]
structure Hom (S₁ S₂ : Split C n) where
  /-- The morphism between the underlying truncated simplicial objects. -/
  F : S₁.X ⟶ S₂.X
  /-- The morphism between distinguished summands in every truncated degree. -/
  f : ∀ m : Fin (n + 1), S₁.s.N m ⟶ S₂.s.N m
  /-- The underlying morphism agrees with the summand morphism on every distinguished summand. -/
  comm : ∀ m : Fin (n + 1),
    S₁.s.ι m ≫ F.app (op ⦋m⦌ₙ) = f m ≫ S₂.s.ι m

attribute [simp, reassoc] Hom.comm

namespace Hom

/-- Two morphisms of split truncated simplicial objects are equal when their maps on every
distinguished summand are equal. -/
@[ext, stacks 017P "extensionality for morphisms of split truncated simplicial objects"]
theorem ext {S₁ S₂ : Split C n} (Φ Ψ : Hom S₁ S₂)
    (h : ∀ m : Fin (n + 1), Φ.f m = Ψ.f m) : Φ = Ψ := sorry

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Cat

/-- Compatibility of identity morphisms with the distinguished summands. -/
@[stacks 017P "identity compatibility for split truncated objects"]
private theorem identity_comm (S : Split C n) (m : Fin (n + 1)) :
    S.s.ι m ≫ (𝟙 S.X : S.X ⟶ S.X).app (op ⦋m⦌ₙ) =
      𝟙 (S.s.N m) ≫ S.s.ι m := sorry

/-- The identity morphism of a split truncated simplicial object. -/
@[stacks 017P "identity morphism of split truncated objects"]
private def identity (S : Split C n) : Hom S S where
  F := 𝟙 S.X
  f := fun m ↦ 𝟙 (S.s.N m)
  comm := identity_comm S

/-- Compatibility of composites with the distinguished summands. -/
@[stacks 017P "composition compatibility for split truncated objects"]
private theorem composition_comm {S₁ S₂ S₃ : Split C n} (Φ : Hom S₁ S₂)
    (Ψ : Hom S₂ S₃) (m : Fin (n + 1)) :
    S₁.s.ι m ≫ (Φ.F ≫ Ψ.F).app (op ⦋m⦌ₙ) =
      (Φ.f m ≫ Ψ.f m) ≫ S₃.s.ι m := sorry

/-- The composite of two morphisms of split truncated simplicial objects. -/
@[stacks 017P "composition of morphisms of split truncated objects"]
private def composition {S₁ S₂ S₃ : Split C n} (Φ : Hom S₁ S₂)
    (Ψ : Hom S₂ S₃) : Hom S₁ S₃ where
  F := Φ.F ≫ Ψ.F
  f := fun m ↦ Φ.f m ≫ Ψ.f m
  comm := composition_comm Φ Ψ

/-- Identity morphisms are left identities for morphisms of split truncated simplicial
objects. -/
@[stacks 017P "left identity law for split truncated objects"]
private theorem identity_comp {S₁ S₂ : Split C n} (Φ : Hom S₁ S₂) :
    composition (identity S₁) Φ = Φ := sorry

/-- Identity morphisms are right identities for morphisms of split truncated simplicial
objects. -/
@[stacks 017P "right identity law for split truncated objects"]
private theorem comp_identity {S₁ S₂ : Split C n} (Φ : Hom S₁ S₂) :
    composition Φ (identity S₂) = Φ := sorry

/-- Composition of morphisms of split truncated simplicial objects is associative. -/
@[stacks 017P "associativity for split truncated objects"]
private theorem composition_assoc {S₁ S₂ S₃ S₄ : Split C n} (Φ : Hom S₁ S₂)
    (Ψ : Hom S₂ S₃) (Χ : Hom S₃ S₄) :
    composition (composition Φ Ψ) Χ = composition Φ (composition Ψ Χ) := sorry

end Cat

/-- Split truncated simplicial objects and splitting-compatible morphisms form a category. -/
@[stacks 017P "category of split truncated simplicial objects"]
instance : Category (Split C n) where
  Hom := Hom
  id := Cat.identity
  comp := Cat.composition
  id_comp := Cat.identity_comp
  comp_id := Cat.comp_identity
  assoc := Cat.composition_assoc

end

end Hom

/-- Two morphisms of split truncated simplicial objects are equal when they agree on every
distinguished summand. -/
@[ext, stacks 017P "category morphism extensionality for split truncated simplicial objects"]
theorem hom_ext {S₁ S₂ : Split C n} (Φ Ψ : S₁ ⟶ S₂)
    (h : ∀ m : Fin (n + 1), Φ.f m = Ψ.f m) : Φ = Ψ := sorry

/-- The underlying truncated simplicial morphism of an identity is the identity. -/
@[simp, stacks 017P "underlying map of an identity of split truncated simplicial objects"]
theorem id_F (S : Split C n) :
    (𝟙 S : S ⟶ S).F = 𝟙 S.X := sorry

/-- The degreewise summand map of an identity is the identity. -/
@[simp, stacks 017P "summand map of an identity of split truncated simplicial objects"]
theorem id_f (S : Split C n) (m : Fin (n + 1)) :
    (𝟙 S : S ⟶ S).f m = 𝟙 (S.s.N m) := sorry

/-- The underlying truncated simplicial morphism of a composite is the composite of the
underlying morphisms. -/
@[simp, stacks 017P "underlying map of a composite of split truncated simplicial objects"]
theorem comp_F {S₁ S₂ S₃ : Split C n} (Φ : S₁ ⟶ S₂) (Ψ : S₂ ⟶ S₃) :
    (Φ ≫ Ψ).F = Φ.F ≫ Ψ.F := sorry

/-- The degreewise summand map of a composite is the composite of the summand maps. -/
@[simp, stacks 017P "summand map of a composite of split truncated simplicial objects"]
theorem comp_f {S₁ S₂ S₃ : Split C n} (Φ : S₁ ⟶ S₂) (Ψ : S₂ ⟶ S₃)
    (m : Fin (n + 1)) :
    (Φ ≫ Ψ).f m = Φ.f m ≫ Ψ.f m := sorry

namespace Hom

/-- A morphism of split truncated simplicial objects commutes with every coproduct injection
in the chosen splitting. -/
@[reassoc, stacks 017P "naturality of splitting cofan injections"]
theorem cofan_inj {S₁ S₂ : Split C n} (Φ : S₁ ⟶ S₂)
    {Δ : (SimplexCategory.Truncated n)ᵒᵖ} (A : Splitting.IndexSet Δ) :
    (S₁.s.cofan Δ).inj A ≫ Φ.F.app Δ =
      Φ.f A.degree ≫ (S₂.s.cofan Δ).inj A := sorry

end Hom

end Split

end CategoryTheory.SimplicialObject.Truncated
