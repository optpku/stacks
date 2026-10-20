module

public import Mathlib.Topology.Constructible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-!
# Local constructibility of relative associated-point containment

For a finitely presented module on a finite-presentation algebraic space over a
scheme, containment of the fibrewise associated points in an open subspace that
is quasi-compact over the base defines a locally constructible locus.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The locus of points of `Y` at which the associated points of the residue-field
fibre module lie in the fibre of an open subspace. -/
def associatedPointsFiberSubset {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (F : X.Modules) (U : OpenSubspace X) : Set Y :=
  setOf fun y : Y ↦
    (setOf fun x : Points (AlgebraicSpace.fiber f y) ↦
        existsEtaleAss ((pullback (AlgebraicSpace.fiberι f y)).obj F) x) ⊆
      Points.map (AlgebraicSpace.fiberι f y) ⁻¹' U.pointsSet

/-- Membership in `associatedPointsFiberSubset` is the fibrewise associated-point
inclusion of `Ass` of the residue-field fibre module into the fibre of `U`. -/
theorem mem_associatedPointsFiberSubset_iff {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (F : X.Modules) (U : OpenSubspace X) (y : Y) :
    y ∈ associatedPointsFiberSubset f F U ↔
      (setOf fun x : Points (AlgebraicSpace.fiber f y) ↦
          existsEtaleAss ((pullback (AlgebraicSpace.fiberι f y)).obj F) x) ⊆
        Points.map (AlgebraicSpace.fiberι f y) ⁻¹' U.pointsSet :=
  Iff.rfl

/-- For a finite-presentation algebraic space over a scheme and a finitely
presented quasi-coherent module, the locus where all associated points of the
residue-field fibre module lie in an open subspace is locally constructible,
provided the open subspace is quasi-compact over the base. -/
@[stacks 0CVV]
theorem associatedPoints_fiber_subset_isLocallyConstructible
    {Y : Scheme.{u}} {X : AlgebraicSpace Y} (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [FinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (U : OpenSubspace X) [QuasiCompact (U.ι ≫ f)] :
    Topology.IsLocallyConstructible (associatedPointsFiberSubset f F U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
