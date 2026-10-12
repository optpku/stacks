/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Specialization
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberAssociatedCycle

/-!
# Specialization of cycles over a discrete valuation ring

The source-facing API uses the canonical scheme-theoretic images, specialization
coefficients and fibre associated cycles. Complete types are retained below.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

#check (AlgebraicGeometry.instUniversallyCatenaryRing_of_isDiscreteValuationRing : ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R],
  UniversallyCatenaryRing.{u, u} R)

#check (AlgebraicGeometry.instUniversallyCatenary_specResidueField : ∀ {X : Scheme.{u}} (x : X),
  UniversallyCatenary (Spec (X.residueField x)))

#check (AlgebraicGeometry.instIsLocallyNoetherian_specResidueField : ∀ {X : Scheme.{u}} (x : X),
  IsLocallyNoetherian (Spec (X.residueField x)))

#check (AlgebraicGeometry.isLocallyNoetherian_of_locallyOfFiniteType_dvr : ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f],
  IsLocallyNoetherian X)

namespace Scheme.Hom

#check (AlgebraicGeometry.Scheme.Hom.instIsLocallyNoetherian_fiber : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S),
  IsLocallyNoetherian (f.fiber s))

#check (AlgebraicGeometry.Scheme.Hom.fiberDimensionFunction : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (s : S),
  f.fiber s → ℤ)

#check (AlgebraicGeometry.Scheme.Hom.fiberDimensionFunction_apply : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (x : f.fiber s),
  f.fiberDimensionFunction s x =
      (f.fiberToSpecResidueField s).relativeDimensionFunction (fun _ ↦ 0) x)

#check (AlgebraicGeometry.Scheme.Hom.instIsDimensionFunction_fiberDimensionFunction : ∀ {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (s : S),
  IsDimensionFunction (f.fiberDimensionFunction s))

#check (AlgebraicGeometry.Scheme.Hom.genericFiber : ∀ {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)),
  Scheme.{u})

#check (AlgebraicGeometry.Scheme.Hom.specialFiber : ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)),
  Scheme.{u})

#check (AlgebraicGeometry.Scheme.Hom.genericFiberι : ∀ {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)),
  f.genericFiber ⟶ X)

#check (AlgebraicGeometry.Scheme.Hom.specialFiberι : ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)),
  f.specialFiber ⟶ X)

#check (AlgebraicGeometry.Scheme.Hom.genericFiber_fiber : ∀ {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)),
  f.genericFiber = f.fiber (genericPoint (Spec (CommRingCat.of R))))

#check (AlgebraicGeometry.Scheme.Hom.specialFiber_fiber : ∀ {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)),
  f.specialFiber = f.fiber (IsLocalRing.closedPoint R))

#check (AlgebraicGeometry.Scheme.Hom.pointImage : ∀ {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber),
  X.IdealSheafData)

#check (AlgebraicGeometry.Scheme.Hom.pointImageSpecial : ∀ {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber),
  f.specialFiber.IdealSheafData)

#check (AlgebraicGeometry.Scheme.Hom.pointImage_spec : ∀ {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber),
  ((f.pointImage z).support : Set X) =
      closure (Set.range (PointClosure.ι z ≫ f.genericFiberι)))

#check (AlgebraicGeometry.Scheme.Hom.support_pointImageSpecial : ∀ {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber),
  ((f.pointImageSpecial z).support : Set (f.specialFiber)) =
      (f.pointImage z).support.preimage f.specialFiberι.continuous)

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
#check (AlgebraicGeometry.Scheme.Hom.cycleSpecializationCoeff f : ∀ (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r)
    (x : f.specialFiber),
  ℤ)

#check (AlgebraicGeometry.Scheme.Hom.cycleSpecializationLocallyFiniteSupport f : ∀ (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r),
  LocallyFiniteSupport (cycleSpecializationCoeff f r α))

#check (AlgebraicGeometry.Scheme.Hom.cycleSpecializationCycle f : ∀ (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r),
  AlgebraicCycle f.specialFiber ℤ)

#check (AlgebraicGeometry.Scheme.Hom.cycleSpecializationCycle_mem_dimensionSubgroup f : ∀ (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r),
  cycleSpecializationCycle f r α ∈
      AlgebraicCycle.dimensionSubgroup
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r)

#check (AlgebraicGeometry.Scheme.Hom.cycleSpecializationValue f : ∀ (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r),
  CycleGroup f.specialFiber
      (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r)

#check (AlgebraicGeometry.Scheme.Hom.cycleSpecializationValue_zero f : ∀ (r : ℕ),
  cycleSpecializationValue f r 0 = 0)

#check (AlgebraicGeometry.Scheme.Hom.cycleSpecializationValue_add f : ∀ (r : ℕ)
    (a b : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r),
  cycleSpecializationValue f r (a + b) =
      cycleSpecializationValue f r a + cycleSpecializationValue f r b)

#check (AlgebraicGeometry.Scheme.Hom.cycleSpecialization f : ∀ (r : ℕ),
  CycleGroup f.genericFiber
        (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r →+
      CycleGroup f.specialFiber
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r)

#check (AlgebraicGeometry.Scheme.Hom.cycleSpecialization_apply f : ∀ (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r)
    (x : f.specialFiber),
  CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (f.cycleSpecialization r α) x =
      cycleSpecializationCoeff f r α x)

#check (AlgebraicGeometry.Scheme.Hom.cycleSpecialization_point f : ∀ (r : ℕ) (z : f.genericFiber)
    (hz : f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))) z = r),
  CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (f.cycleSpecialization r
          (CycleGroup.point
            (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r z hz)) =
      CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (IdealSheafData.associatedCycle (f.pointImageSpecial z)
          (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r))

end Scheme.Hom

namespace Scheme.Modules

#check (AlgebraicGeometry.Scheme.Modules.fiberAssociatedCycle : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsCoherent] [IsLocallyNoetherian X] (s : S) (r : ℕ)
    [IsLocallyNoetherian (f.fiber s)],
  CycleGroup (f.fiber s) (f.fiberDimensionFunction s) r)

#check (AlgebraicGeometry.Scheme.Modules.fiberAssociatedCycle_toAlgebraicCycle : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsCoherent] [IsLocallyNoetherian X] (s : S) (r : ℕ)
    [IsLocallyNoetherian (f.fiber s)] (x : f.fiber s),
  CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r
        (fiberAssociatedCycle f F s r) x =
      associatedCycle ((pullback (f.fiberι s)).obj F)
        (f.fiberDimensionFunction s) r x)

#check (AlgebraicGeometry.Scheme.Modules.fiberAssociatedCycle_apply : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsCoherent] [IsLocallyNoetherian X] (s : S) (r : ℕ)
    [IsLocallyNoetherian (f.fiber s)] (x : f.fiber s),
  CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r
        (fiberAssociatedCycle f F s r) x =
      associatedCycle ((pullback (f.fiberι s)).obj F)
        (f.fiberDimensionFunction s) r x)

end Scheme.Modules

end AlgebraicGeometry
