/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ResidueField

/-!
# Fibre degrees of scheme morphisms

This file owns the residue-field algebra and numerical degree of a fibre of a
scheme morphism, together with uniform boundedness predicates.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The global-sections ring of the fibre of `f` over a point `y` of its target. -/
abbrev fiberGlobalSections (f : X ⟶ Y) (y : Y) :=
  Scheme.Γ.obj (Opposite.op (f.fiber y))

/-- The residue-field algebra structure on the global sections of a fibre. -/
@[reducible] instance fiberGlobalSectionsAlgebra (f : X ⟶ Y) (y : Y) :
    Algebra (Y.residueField y) (fiberGlobalSections f y) :=
  globalSectionsAlgebra (f.fiberToSpecResidueField y)

/-- The degree of a fibre, measured as the finite rank of its global-sections algebra over the
residue field of the target point. -/
abbrev fiberDegree (f : X ⟶ Y) (y : Y) : ℕ :=
  Module.finrank (Y.residueField y) (fiberGlobalSections f y)

/-- The global-sections ring of the pullback of `f` along a field-valued point
of its target. -/
abbrev fieldValuedPointPullbackGlobalSections (f : X ⟶ Y)
    {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ Y) :=
  Scheme.Γ.obj (Opposite.op (pullback f g : Scheme))

/-- The canonical scalar action on global sections of a field-valued pullback. -/
@[reducible] instance fieldValuedPointPullbackGlobalSectionsAlgebra (f : X ⟶ Y)
    {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ Y) :
    Algebra k (fieldValuedPointPullbackGlobalSections f g) :=
  globalSectionsAlgebra (pullback.snd f g)

/-- The degree of the pullback of `f` along a field-valued point, measured over
the source field. -/
abbrev fieldValuedPointPullbackDegree (f : X ⟶ Y)
    {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ Y) : ℕ :=
  Module.finrank k (fieldValuedPointPullbackGlobalSections f g)

/-- A number bounds the fibre degrees of a morphism when every residue-field fibre is finite and
has degree at most that number. -/
def degreesOfFibresBoundedBy (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ y : Y,
    IsFinite (f.fiberToSpecResidueField y) ∧
      f.fiberDegree y ≤ n

/-- Extract finiteness of the fibre over a specified target point from a degree bound. -/
theorem degreesOfFibresBoundedBy.isFinite
    {f : X ⟶ Y} {n : ℕ} (h : degreesOfFibresBoundedBy f n) (y : Y) :
    IsFinite (f.fiberToSpecResidueField y) := sorry

/-- Extract the numerical degree bound at a specified target point. -/
theorem degreesOfFibresBoundedBy.fiberDegree_le
    {f : X ⟶ Y} {n : ℕ} (h : degreesOfFibresBoundedBy f n) (y : Y) :
    f.fiberDegree y ≤ n := sorry

/-- Unfold the pointwise finiteness and degree-bound condition. -/
theorem degreesOfFibresBoundedBy_iff (f : X ⟶ Y) (n : ℕ) :
    degreesOfFibresBoundedBy f n ↔
      ∀ y : Y, IsFinite (f.fiberToSpecResidueField y) ∧ f.fiberDegree y ≤ n := sorry

/-- A scheme morphism has universally bounded fibres when one natural number bounds the degrees
of every residue-field fibre. -/
def universallyBoundedFibres (f : X ⟶ Y) : Prop :=
  ∃ n : ℕ, degreesOfFibresBoundedBy f n

/-- Unfold universal fibre boundedness into the existence of a numerical degree bound. -/
theorem universallyBoundedFibres_iff (f : X ⟶ Y) :
    universallyBoundedFibres f ↔ ∃ n : ℕ, degreesOfFibresBoundedBy f n := sorry

end Scheme.Hom
end AlgebraicGeometry
