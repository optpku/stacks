module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.Field
import StacksCheckRecall

/-!
# Conditions on a point of an algebraic space locally of finite type over a field

For an algebraic space locally of finite type over a field, a point is closed with
no nontrivial specialization into it if and only if it is isolated, if and only if
the étale-local dimension there vanishes, if and only if the structure morphism is
quasi-finite at that point. If the algebraic space is decent, vanishing of the
local topological Krull dimension of the space of points is equivalent to these.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.18.7: The closed-specialization, isolation, dimension, and
quasi-finiteness conditions are equivalent. -/
@[stacks 0AC9] #check (AlgebraicGeometry.AlgebraicSpace.tfae_isClosed_specializes_isOpen_dimensionAt_quasiFiniteAt :
    ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X),
    List.TFAE
      [ (IsClosed ({x} : Set (Points X)) ∧
          (∀ x' : Points X, Specializes x' x → x' = x))
      , IsOpen ({x} : Set (Points X))
      , dimensionAt x = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ])

/- Lemma 68.18.7: For a decent space, vanishing local topological Krull
dimension is also equivalent to the other four conditions. -/
@[stacks 0AC9] #check (AlgebraicGeometry.AlgebraicSpace.tfae_topologicalKrullDimAt_isClosed_isOpen_dimensionAt_quasiFiniteAt :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
    [IsDecent X] (x : Points X),
    List.TFAE
      [ topologicalKrullDimAt x = (0 : WithBot ℕ∞)
      , (IsClosed ({x} : Set (Points X)) ∧
          (∀ x' : Points X, Specializes x' x → x' = x))
      , IsOpen ({x} : Set (Points X))
      , dimensionAt x = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ])

#check (AlgebraicGeometry.AlgebraicSpace.isClosed_specializes_iff_isOpen_singleton :
    ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X),
    (IsClosed ({x} : Set (Points X)) ∧
        (∀ x' : Points X, Specializes x' x → x' = x)) ↔
      IsOpen ({x} : Set (Points X)))

#check (AlgebraicGeometry.AlgebraicSpace.isOpen_singleton_iff_dimensionAt_eq_zero :
    ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X),
    IsOpen ({x} : Set (Points X)) ↔ dimensionAt x = (0 : WithBot ℕ∞))

#check (AlgebraicGeometry.AlgebraicSpace.dimensionAt_eq_zero_iff_quasiFiniteAt :
    ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X),
    dimensionAt x = (0 : WithBot ℕ∞) ↔ QuasiFiniteAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.topologicalKrullDimAt_eq_zero_iff_quasiFiniteAt :
    ∀ {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] [IsDecent X]
    (x : Points X),
    topologicalKrullDimAt x = (0 : WithBot ℕ∞) ↔ QuasiFiniteAt f x)

