module

public import Mathlib.Order.Category.Preord
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.CategoryTheory.InverseSystem.Preorder

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism is a smooth inverse limit if its domain is a nonempty directed
inverse limit of schemes smooth over its codomain, with affine transition maps
and compatible structure morphisms. -/
def IsSmoothInverseLimit {T S : Scheme.{u}} (g : T ⟶ S) : Prop :=
  ∃ (I : Preord.{u}) (DS : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj T ⟶ DS)
    (hcS : IsLimit ({ pt := T, π := π } : Cone DS))
    (gi : ∀ i : I, DS.obj (OrderDual.toDual i) ⟶ S),
    Nonempty I ∧ IsDirected I (· ≤ ·) ∧
      (∀ {i j : I} (hij : i ≤ j),
        IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)) ∧
      (∀ i : I, Smooth (gi i)) ∧
      (∀ {i j : I} (hij : i ≤ j),
        OrderDualInverseSystem.transitionMap DS hij ≫ gi i = gi j) ∧
      (∀ i : I, π.app (OrderDual.toDual i) ≫ gi i = g)

/-- A smooth inverse limit is exactly a compatible nonempty directed presentation
by smooth schemes with affine transitions and a limiting cone on the given domain. -/
theorem isSmoothInverseLimit_iff {T S : Scheme.{u}} (g : T ⟶ S) :
    IsSmoothInverseLimit g ↔
      ∃ (I : Preord.{u}) (DS : OrderDual I ⥤ Scheme.{u})
        (π : (Functor.const (OrderDual I)).obj T ⟶ DS)
        (hcS : IsLimit ({ pt := T, π := π } : Cone DS))
        (gi : ∀ i : I, DS.obj (OrderDual.toDual i) ⟶ S),
        Nonempty I ∧ IsDirected I (· ≤ ·) ∧
          (∀ {i j : I} (hij : i ≤ j),
            IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)) ∧
          (∀ i : I, Smooth (gi i)) ∧
          (∀ {i j : I} (hij : i ≤ j),
            OrderDualInverseSystem.transitionMap DS hij ≫ gi i = gi j) ∧
          (∀ i : I, π.app (OrderDual.toDual i) ≫ gi i = g) := Iff.rfl

/-- A compatible limiting cone over a nonempty directed system of smooth schemes
with affine transition maps presents a smooth inverse limit morphism. -/
theorem isSmoothInverseLimit_of_presentation
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (DS : OrderDual I ⥤ Scheme.{u})
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
    (gi : ∀ i : I, DS.obj (OrderDual.toDual i) ⟶ S)
    [∀ i : I, Smooth (gi i)]
    (hgi : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DS hij ≫ gi i = gi j)
    (cS : Cone DS) (hcS : IsLimit cS) (g : cS.pt ⟶ S)
    (hg : ∀ i : I, cS.π.app (OrderDual.toDual i) ≫ gi i = g) :
    IsSmoothInverseLimit g := by
  exact ⟨Preord.of I, DS, cS.π, hcS, gi, inferInstance, inferInstance,
    inferInstance, inferInstance, hgi, hg⟩

end AlgebraicGeometry.Scheme.Hom
