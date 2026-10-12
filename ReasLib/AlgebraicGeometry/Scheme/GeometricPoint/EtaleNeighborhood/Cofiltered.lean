/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.FieldTheory.IsAlgClosed.Basic

open CategoryTheory Opposite

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme.GeometricPoint

/-- The étale neighborhoods of a field-valued scheme morphism, represented by the category
of elements of its lift functor. -/
abbrev EtaleNeighborhoodOf {S : Scheme.{u}} {K : Type u} [Field K]
    (point : Spec (.of K) ⟶ S) :=
  (Etale.forget S ⋙ coyoneda.obj (op (Over.mk point))).Elements

namespace EtaleNeighborhood

/-- The category of étale neighborhoods of a geometric point is cofiltered. -/
theorem isCofiltered {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (point : Spec (.of K) ⟶ S) :
    IsCofiltered (EtaleNeighborhoodOf point) := sorry

/-- Two étale neighborhoods of a geometric point admit a common refining neighborhood
with morphisms to both. -/
theorem exists_commonRefinement {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (point : Spec (.of K) ⟶ S) (U₁ U₂ : EtaleNeighborhoodOf point) :
    ∃ U : EtaleNeighborhoodOf point, Nonempty ((U ⟶ U₁) × (U ⟶ U₂)) := sorry

/-- Parallel morphisms of étale neighborhoods of a geometric point become equal after
precomposition with a morphism from a further neighborhood. -/
theorem exists_equalizingRefinement {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (point : Spec (.of K) ⟶ S) {U U' : EtaleNeighborhoodOf point} (h₁ h₂ : U ⟶ U') :
    ∃ (U'' : EtaleNeighborhoodOf point) (h : U'' ⟶ U), h ≫ h₁ = h ≫ h₂ := sorry

end EtaleNeighborhood

end AlgebraicGeometry.Scheme.GeometricPoint
