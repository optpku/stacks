module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import stacks_project.Chap101.Lemma_101_36_4_Etale
public import stacks_project.Chap101.Remark_101_19_5_AutomorphismGroup

/-!
# Étale morphisms that are equivalences on algebraically closed points

An étale morphism of algebraic stacks that induces isomorphisms of
automorphism groups at all points and is an equivalence on morphisms from
`Spec(k)` for every algebraically closed field `k` is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.45.7: let `f : X ⟶ Y` be a morphism of algebraic stacks. Assume
`f` is étale, `f` induces an isomorphism between automorphism groups at
points (Remark 101.19.5), and for every algebraically closed field `k` the
functor `Mor(Spec(k), X) ⟶ Mor(Spec(k), Y)` is an equivalence. Then `f` is
an isomorphism. Here `Mor(Spec(k), -)` is Hom from
`GroupoidsOver.slice (Over.mk σ)` for `σ : Spec (.of k) ⟶ S`, and the
functor is `Bicategory.postcomp` of `f`. An isomorphism of algebraic stacks
is `(toBasedFunctor f).IsEquivalence`. -/
@[stacks 0DUD]
theorem isEquivalence_of_etale_of_forall_isIsoAt {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Etale f]
    (h_aut : ∀ x : |X|, automorphismGroup.IsIsoAt f x)
    (h_eq :
      ∀ {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S),
        (Bicategory.postcomp (GroupoidsOver.slice (Over.mk σ)) f).IsEquivalence) :
    (toBasedFunctor f).IsEquivalence :=
  sorry

/-- If `f` is étale, induces isomorphisms of automorphism groups at all points
of `|X|`, and `fiberFunctor f (Over.mk σ)` is an equivalence for every
algebraically closed field `k` and structure map `σ : Spec (.of k) ⟶ S`,
then `f` is an isomorphism of algebraic stacks. -/
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
