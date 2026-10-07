module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Unramified morphisms and relative differentials

This file characterizes formal unramifiedness, unramifiedness, and G-unramifiedness in terms of
the vanishing of the sheaf of relative differentials.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A scheme morphism is formally unramified if and only if its sheaf of relative differentials
vanishes. -/
theorem formallyUnramified_iff_isZero_relativeDifferentials
    (f : X ⟶ S) :
    FormallyUnramified f ↔ CategoryTheory.Limits.IsZero (Ω[f.toShHom]) := sorry

/-- The sheaf of relative differentials of a monomorphism of schemes vanishes. -/
theorem isZero_relativeDifferentials_of_mono
    (f : X ⟶ S) [Mono f] :
    CategoryTheory.Limits.IsZero (Ω[f.toShHom]) := sorry

/-- A scheme morphism is unramified if and only if it is locally of finite type and its sheaf of
relative differentials vanishes. -/
theorem unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials
    (f : X ⟶ S) :
    Unramified f ↔
      LocallyOfFiniteType f ∧ CategoryTheory.Limits.IsZero (Ω[f.toShHom]) := sorry

/-- A scheme morphism is G-unramified if and only if it is locally of finite presentation and its
sheaf of relative differentials vanishes. -/
theorem GUnramified.iff_differentials
    (f : X ⟶ S) :
    GUnramified f ↔
      LocallyOfFinitePresentation f ∧ CategoryTheory.Limits.IsZero (Ω[f.toShHom]) := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom.Conormal.Differentials

variable {Z X S : Scheme.{u}}

/-- For a formally unramified morphism, the canonical comparison on relative differentials is an
epimorphism. -/
theorem comparison_epi_of_formallyUnramified (h : Z ⟶ X) [FormallyUnramified h]
    (f : X ⟶ S) : Epi (comparison h f) := sorry

end AlgebraicGeometry.Scheme.Hom.Conormal.Differentials
