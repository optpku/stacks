/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberAssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberSupportDimension
public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Specialization

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
variable (F : X.Modules) [F.IsCoherent] (r : ℕ)

/-- The support dimension of a coherent module on the special fibre is bounded by
the degree bound on its generic-fibre support when the module is flat over the base. -/
theorem topologicalKrullDim_moduleSupport_specialFiber_le
    (hflat : ∀ x : X, Module.FlatAlong (f.stalkMap x).hom (RingedSpace.stalkModuleCat F x))
    (hK : fiberSupportDimension f F
      (genericPoint (Spec (CommRingCat.of R))) ≤ (r : WithBot ℕ∞)) :
    fiberSupportDimension f F (IsLocalRing.closedPoint R) ≤ (r : WithBot ℕ∞) :=
  sorry

/-- Specialization of the degree-`r` associated cycle of a module flat over a
discrete valuation ring is the degree-`r` associated cycle on the special fibre. -/
theorem cycleSpecialization_associatedCycle
    (hflat : ∀ x : X, Module.FlatAlong (f.stalkMap x).hom (RingedSpace.stalkModuleCat F x))
    (hK : fiberSupportDimension f F
      (genericPoint (Spec (CommRingCat.of R))) ≤ (r : WithBot ℕ∞)) :
    Hom.cycleSpecialization f r
        (fiberAssociatedCycle f F
          (genericPoint (Spec (CommRingCat.of R))) r) =
      fiberAssociatedCycle f F (IsLocalRing.closedPoint R) r :=
  sorry

end AlgebraicGeometry.Scheme.Modules
