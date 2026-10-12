/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Finite presentation versus finite type

Finite presentation of a scheme morphism strengthens finite type: local finite presentation
implies local finite type, while the quasi-compact component is already part of the project-level
finite-presentation class.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite-presentation scheme morphism is finite type. -/
theorem FinitePresentation.finiteType
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : FinitePresentation f) :
    FiniteType f := sorry

/-- A finite-presentation scheme morphism is canonically a finite-type morphism. -/
instance instFiniteTypeOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [FinitePresentation f] :
    FiniteType f := sorry

end AlgebraicGeometry.Scheme.Hom
