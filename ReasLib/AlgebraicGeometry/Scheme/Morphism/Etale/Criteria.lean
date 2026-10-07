module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Criteria for étale morphisms
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.Etale

/-- A scheme morphism is étale exactly when it is locally of finite presentation, flat, and has
étale fibres over every point of the target. -/
theorem iff_locallyOfFinitePresentation_flat_etaleFibers
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔
      LocallyOfFinitePresentation f ∧ Flat f ∧
        (∀ s : S, Etale (f.fiberToSpecResidueField s)) := sorry

/-- A scheme morphism is étale exactly when it is flat, unramified, and locally of finite
presentation. -/
theorem iff_flat_and_unramified_and_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔ Flat f ∧ Unramified f ∧ LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry.Etale
