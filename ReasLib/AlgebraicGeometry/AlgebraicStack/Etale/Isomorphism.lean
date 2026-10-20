module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Etale

/-- Étaleness of morphisms of algebraic stacks is invariant under
2-isomorphism. -/
theorem iso_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f g : X ⟶ Y} (α : f ≅ g) :
    Etale f ↔ Etale g := sorry

end AlgebraicGeometry.AlgebraicStack.Etale

namespace AlgebraicGeometry.AlgebraicStack

/-- An étale morphism of algebraic stacks that induces isomorphisms of
automorphism groups at all points and equivalences on morphism groupoids from
every algebraically closed field spectrum is an equivalence over the base. -/
theorem isEquivalence_of_etale_of_forall_isIsoAt {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Etale f]
    (h_aut : ∀ x : |X|, automorphismGroup.IsIsoAt f x)
    (h_eq :
      ∀ {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S),
        (Bicategory.postcomp (GroupoidsOver.slice (Over.mk σ)) f).IsEquivalence) :
    (toBasedFunctor f).IsEquivalence :=
  sorry

/-- An étale morphism of algebraic stacks that induces isomorphisms of
automorphism groups at all points and whose fiber functors at all algebraically
closed field-valued points are equivalences is an equivalence over the base. -/
theorem isEquivalence_of_etale_of_forall_isIsoAt_of_fiberFunctor
    {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (f : X ⟶ Y) [Etale f]
    (h_aut : ∀ x : |X|, automorphismGroup.IsIsoAt f x)
    (h_eq :
      ∀ {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S),
        (fiberFunctor f (Over.mk σ)).IsEquivalence) :
    (toBasedFunctor f).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicStack
