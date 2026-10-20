module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Dimension

/-!
# Pointwise dimension criteria over a field

For algebraic spaces locally of finite type over a field, isolation and vanishing
étale-local dimension characterize quasi-finiteness at a point. For decent spaces,
local topological Krull dimension gives the same criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For an algebraic space locally of finite type over a field, closedness with no
nontrivial specialization into a point, openness of its singleton, vanishing
étale-local dimension, and quasi-finiteness at that point are equivalent. -/
theorem tfae_isClosed_specializes_isOpen_dimensionAt_quasiFiniteAt {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X) :
    List.TFAE
      [ (IsClosed ({x} : Set (Points X)) ∧
          (∀ x' : Points X, Specializes x' x → x' = x))
      , IsOpen ({x} : Set (Points X))
      , dimensionAt x = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ] :=
  sorry

/-- For a decent algebraic space locally of finite type over a field, vanishing
local topological Krull dimension, closedness with no nontrivial specialization
into a point, openness of its singleton, vanishing étale-local dimension, and
quasi-finiteness at that point are equivalent. -/
theorem tfae_topologicalKrullDimAt_isClosed_isOpen_dimensionAt_quasiFiniteAt
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
    [IsDecent X] (x : Points X) :
    List.TFAE
      [ topologicalKrullDimAt x = (0 : WithBot ℕ∞)
      , (IsClosed ({x} : Set (Points X)) ∧
          (∀ x' : Points X, Specializes x' x → x' = x))
      , IsOpen ({x} : Set (Points X))
      , dimensionAt x = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ] :=
  sorry

/-- For an algebraic space locally of finite type over a field, a point is closed
with no nontrivial specialization into it if and only if its singleton is open. -/
theorem isClosed_specializes_iff_isOpen_singleton {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X) :
    (IsClosed ({x} : Set (Points X)) ∧
        (∀ x' : Points X, Specializes x' x → x' = x)) ↔
      IsOpen ({x} : Set (Points X)) :=
  sorry

/-- For an algebraic space locally of finite type over a field, a point is isolated
if and only if the étale-local dimension there vanishes. -/
theorem isOpen_singleton_iff_dimensionAt_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X) :
    IsOpen ({x} : Set (Points X)) ↔ dimensionAt x = (0 : WithBot ℕ∞) :=
  sorry

/-- For an algebraic space locally of finite type over a field, the étale-local
dimension at a point vanishes if and only if the structure morphism is
quasi-finite at that point. -/
theorem dimensionAt_eq_zero_iff_quasiFiniteAt {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] (x : Points X) :
    dimensionAt x = (0 : WithBot ℕ∞) ↔ QuasiFiniteAt f x :=
  sorry

/-- For a decent algebraic space locally of finite type over a field, vanishing of
the local topological Krull dimension of the space of points is equivalent to
quasi-finiteness of the structure morphism at that point. -/
theorem topologicalKrullDimAt_eq_zero_iff_quasiFiniteAt {S : Scheme.{u}}
    {X : AlgebraicSpace S} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f] [IsDecent X]
    (x : Points X) :
    topologicalKrullDimAt x = (0 : WithBot ℕ∞) ↔ QuasiFiniteAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
