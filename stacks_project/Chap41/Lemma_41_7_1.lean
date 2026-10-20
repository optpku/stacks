module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 41.7.1: For a scheme morphism `f : X ⟶ S`, the conditions that `f` is
unramified and a monomorphism, unramified and universally injective, locally of finite type
and a monomorphism, universally injective and formally unramified of local finite type, or
of local finite type with every fiber empty or canonically isomorphic to `Spec κ(s)`, are
equivalent. -/
@[stacks 05VH]
#check (AlgebraicGeometry.tfae_unramified_mono :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
    List.TFAE [
      AlgebraicGeometry.Unramified f ∧ Mono f,
      AlgebraicGeometry.Unramified f ∧ AlgebraicGeometry.UniversallyInjective f,
      AlgebraicGeometry.LocallyOfFiniteType f ∧ Mono f,
      AlgebraicGeometry.UniversallyInjective f ∧
        AlgebraicGeometry.LocallyOfFiniteType f ∧ AlgebraicGeometry.FormallyUnramified f,
      AlgebraicGeometry.LocallyOfFiniteType f ∧
        ∀ s : S, IsEmpty (f.fiber s) ∨ IsIso (f.fiberToSpecResidueField s)])
