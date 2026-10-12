/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GenericSpecialMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Specialization

/-!
# Specialization and proper pushforward of cycles

Specialization of cycles over a discrete valuation ring commutes with proper
pushforward between schemes locally of finite type over the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Over a discrete valuation ring, specialization of `r`-cycles commutes with
proper pushforward between schemes locally of finite type over the base, as an
equality of additive homomorphisms. -/
theorem cycleSpecialization_comp_mapHom
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (r : ℕ) :
    (Y.hom.cycleSpecialization r).comp
      (mapHom (genericFiberMap f)
        (X.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
        (Y.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) =
      (mapHom (specialFiberMap f)
        (X.hom.fiberDimensionFunction (IsLocalRing.closedPoint R))
        (Y.hom.fiberDimensionFunction (IsLocalRing.closedPoint R)) r).comp
        (X.hom.cycleSpecialization r) := sorry

/-- Specialization of an `r`-cycle on the generic fibre, then proper pushforward
on the special fibre, agrees with proper pushforward on the generic fibre
followed by specialization. -/
theorem cycleSpecialization_mapHom
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (r : ℕ)
    (α : CycleGroup X.hom.genericFiber
      (X.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    Y.hom.cycleSpecialization r
      (mapHom (genericFiberMap f)
        (X.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
        (Y.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r α) =
      mapHom (specialFiberMap f)
        (X.hom.fiberDimensionFunction (IsLocalRing.closedPoint R))
        (Y.hom.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (X.hom.cycleSpecialization r α) := sorry

end AlgebraicGeometry.CycleGroup
