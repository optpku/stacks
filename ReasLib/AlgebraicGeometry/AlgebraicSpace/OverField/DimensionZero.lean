module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Zero-dimensional algebraic spaces over a field

For algebraic spaces locally of finite type over a field, discreteness and
dimension at most zero characterize local quasi-finiteness. Decent spaces with
finitely many points satisfy these conditions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For an algebraic space locally of finite type over a field, discreteness of
its space of points, topological Krull dimension at most zero, étale-local
dimension at most zero, and local quasi-finiteness of its structure morphism are
equivalent. -/
theorem tfae_discrete_dimension_locallyQuasiFinite {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] :
    List.TFAE
      [ DiscreteTopology (Points X)
      , topologicalKrullDim (Points X) ≤ 0
      , dimension X ≤ 0
      , LocallyQuasiFinite f ] :=
  sorry

/-- A decent algebraic space locally of finite type over a field with finitely
many points has a locally quasi-finite structure morphism. -/
instance locallyQuasiFinite_of_isDecent_finite {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] [IsDecent X]
    [Finite (Points X)] : LocallyQuasiFinite f :=
  sorry

/-- For an algebraic space locally of finite type over a field, the space of
points is discrete if and only if its topological Krull dimension is at most
zero. -/
theorem discreteTopology_iff_topologicalKrullDim_le_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] :
    DiscreteTopology (Points X) ↔ topologicalKrullDim (Points X) ≤ 0 :=
  (tfae_discrete_dimension_locallyQuasiFinite f).out 0 1

/-- For an algebraic space locally of finite type over a field, the topological
Krull dimension of its space of points is at most zero if and only if its
étale-local dimension is at most zero. -/
theorem topologicalKrullDim_le_zero_iff_dimension_le_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] :
    topologicalKrullDim (Points X) ≤ 0 ↔ dimension X ≤ 0 :=
  (tfae_discrete_dimension_locallyQuasiFinite f).out 1 2

/-- For an algebraic space locally of finite type over a field, its étale-local
dimension is at most zero if and only if its structure morphism is locally
quasi-finite. -/
theorem dimension_le_zero_iff_locallyQuasiFinite {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] :
    dimension X ≤ 0 ↔ LocallyQuasiFinite f :=
  (tfae_discrete_dimension_locallyQuasiFinite f).out 2 3

end AlgebraicGeometry.AlgebraicSpace
