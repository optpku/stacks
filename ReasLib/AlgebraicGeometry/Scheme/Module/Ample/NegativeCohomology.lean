module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth

/-!
# Negative cohomology of ample twists

This file records eventual vanishing of degree-zero and degree-one cohomology for sufficiently
negative twists of coherent modules under suitable associated-point or stalk-depth hypotheses.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsAmple

/-- If the associated points of a coherent module on a proper scheme over a field are disjoint
from the closed points, then its degree-zero cohomology vanishes after every sufficiently
negative twist by an ample invertible module. -/
theorem twistZeroCohomology_eventually_isZero
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L F : X.Modules) [L.Invertible] [IsAmple L] [F.IsCoherent]
    (h : Disjoint (associatedPoints F) (closedPoints X)) :
    ∃ b : ℤ, ∀ d : ℤ, d ≤ b →
      IsZero (Scheme.Hom.cohomology f (F ⊗ L ^⊗ d) 0) := sorry

/-- If a coherent module on a proper scheme over a field has stalk depth at least two at every
closed point, then its degree-one cohomology vanishes after every sufficiently negative twist by
an ample invertible module. -/
theorem twistFirstCohomology_eventually_isZero
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (L F : X.Modules) [L.Invertible] [IsAmple L] [F.IsCoherent]
    (hdepth : ∀ x : X, x ∈ closedPoints X →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x)) :
    ∃ b : ℤ, ∀ d : ℤ, d ≤ b →
      IsZero (Scheme.Hom.cohomology f (F ⊗ L ^⊗ d) 1) := sorry

end AlgebraicGeometry.Scheme.Modules.IsAmple
