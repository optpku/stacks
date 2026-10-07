module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberSupportDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.DimensionOne
public import ReasLib.RingTheory.Catenary.Field

/-!
# Specialization of cycles over a discrete valuation ring

This file constructs the specialization map `sp_{X/R} : Z_r(X_K) → Z_r(X_κ)` on
cycles of a scheme locally of finite type over a discrete valuation ring, together
with associated cycles of coherent modules on scheme-theoretic fibres.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A discrete valuation ring is universally catenary. -/
instance instUniversallyCatenaryRing_of_isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    UniversallyCatenaryRing.{u, u} R := sorry

/-- The spectrum of the residue field of a scheme point is universally catenary. -/
instance instUniversallyCatenary_specResidueField {X : Scheme.{u}} (x : X) :
    UniversallyCatenary (Spec (X.residueField x)) := sorry

/-- The spectrum of the residue field of a scheme point is locally Noetherian. -/
instance instIsLocallyNoetherian_specResidueField {X : Scheme.{u}} (x : X) :
    IsLocallyNoetherian (Spec (X.residueField x)) := sorry

/-- A scheme locally of finite type over a discrete valuation ring is locally Noetherian. -/
theorem isLocallyNoetherian_of_locallyOfFiniteType_dvr
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    IsLocallyNoetherian X := sorry

namespace Scheme.Hom

/-- Scheme-theoretic fibres of a locally finite type morphism are locally Noetherian. -/
instance instIsLocallyNoetherian_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S) :
    IsLocallyNoetherian (f.fiber s) := sorry

/-- The standard dimension function on a scheme-theoretic fibre, obtained by viewing the
fibre as a scheme locally of finite type over the residue field of the base point. -/
noncomputable abbrev fiberDimensionFunction {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    f.fiber s → ℤ :=
  (f.fiberToSpecResidueField s).relativeDimensionFunction (fun _ ↦ 0)

/-- The fibre dimension function is the relative dimension function of
`fiberToSpecResidueField` against the zero function on the residue field. -/
theorem fiberDimensionFunction_apply {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (x : f.fiber s) :
    f.fiberDimensionFunction s x =
      (f.fiberToSpecResidueField s).relativeDimensionFunction (fun _ ↦ 0) x := sorry

/-- The fibre dimension function is a dimension function. -/
instance instIsDimensionFunction_fiberDimensionFunction {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) :
    IsDimensionFunction (f.fiberDimensionFunction s) := sorry

/-- The generic fibre `X_K` of a morphism to the spectrum of a domain. -/
noncomputable abbrev genericFiber {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  f.fiber (genericPoint (Spec (CommRingCat.of R)))

/-- The closed fibre `X_κ` of a morphism to the spectrum of a local ring. -/
noncomputable abbrev specialFiber {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  f.fiber (IsLocalRing.closedPoint R)

/-- The canonical immersion of the generic fibre into `X`. -/
noncomputable abbrev genericFiberι {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    f.genericFiber ⟶ X :=
  f.fiberι (genericPoint (Spec (CommRingCat.of R)))

/-- The canonical immersion of the special fibre into `X`. -/
noncomputable abbrev specialFiberι {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    f.specialFiber ⟶ X :=
  f.fiberι (IsLocalRing.closedPoint R)

/-- The generic fibre is the scheme-theoretic fibre over the generic point of `Spec R`. -/
theorem genericFiber_fiber {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    f.genericFiber = f.fiber (genericPoint (Spec (CommRingCat.of R))) := sorry

/-- The special fibre is the scheme-theoretic fibre over the closed point of `Spec R`. -/
theorem specialFiber_fiber {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    f.specialFiber = f.fiber (IsLocalRing.closedPoint R) := sorry

/-- The scheme-theoretic image in `X` of the reduced closure of a point of the generic
fibre. -/
noncomputable def pointImage {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber) : X.IdealSheafData :=
  (PointClosure.ι z ≫ f.genericFiberι).ker

/-- The closed subscheme of the special fibre obtained by pulling back the scheme-theoretic
image of a generic-fibre point. -/
noncomputable def pointImageSpecial {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber) :
    f.specialFiber.IdealSheafData :=
  (f.pointImage z).comap f.specialFiberι

/-- The scheme-theoretic image of the reduced closure of a generic-fibre point is the
closure of its image in `X`. -/
theorem pointImage_spec {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber) :
    ((f.pointImage z).support : Set X) =
      closure (Set.range (PointClosure.ι z ≫ f.genericFiberι)) := sorry

/-- The support of the special-fibre pullback of a point image is the preimage of the
ambient scheme-theoretic image. -/
theorem support_pointImageSpecial {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber) :
    ((f.pointImageSpecial z).support : Set (f.specialFiber)) =
      (f.pointImage z).support.preimage f.specialFiberι.continuous := sorry

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]

/-- The coefficient of a specialized cycle at a special-fibre point. -/
noncomputable def cycleSpecializationCoeff (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r)
    (x : f.specialFiber) : ℤ :=
  ∑ᶠ z : f.genericFiber,
    CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r α z *
      (CycleGroup.toAlgebraicCycle
          (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
          (IdealSheafData.associatedCycle (f.pointImageSpecial z)
            (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r)) x

/-- The coefficient function of specialization has locally finite support. -/
theorem cycleSpecializationLocallyFiniteSupport (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    LocallyFiniteSupport (cycleSpecializationCoeff f r α) := sorry

/-- The underlying algebraic cycle of specialization. -/
noncomputable def cycleSpecializationCycle (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    AlgebraicCycle f.specialFiber ℤ where
  toFun := cycleSpecializationCoeff f r α
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    cycleSpecializationLocallyFiniteSupport f r α x

/-- The underlying specialization cycle is supported in dimension `r`. -/
theorem cycleSpecializationCycle_mem_dimensionSubgroup (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    cycleSpecializationCycle f r α ∈
      AlgebraicCycle.dimensionSubgroup
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r := sorry

/-- The underlying degree-`r` cycle of specialization. -/
noncomputable def cycleSpecializationValue (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    CycleGroup f.specialFiber
      (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r :=
  ⟨cycleSpecializationCycle f r α,
    cycleSpecializationCycle_mem_dimensionSubgroup f r α⟩

/-- Specialization sends the zero cycle to zero. -/
theorem cycleSpecializationValue_zero (r : ℕ) :
    cycleSpecializationValue f r 0 = 0 := sorry

/-- Specialization preserves addition of degree-`r` cycles. -/
theorem cycleSpecializationValue_add (r : ℕ)
    (a b : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    cycleSpecializationValue f r (a + b) =
      cycleSpecializationValue f r a + cycleSpecializationValue f r b := sorry

/-- The specialization map `sp_{X/R}` on degree-`r` cycles of the generic fibre. -/
noncomputable def cycleSpecialization (r : ℕ) :
    CycleGroup f.genericFiber
        (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r →+
      CycleGroup f.specialFiber
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r where
  toFun := cycleSpecializationValue f r
  map_zero' := cycleSpecializationValue_zero f r
  map_add' := cycleSpecializationValue_add f r

/-- Coefficients of specialization are the locally finite sum of input coefficients times
the associated cycles of special-fibre point images. -/
theorem cycleSpecialization_apply (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r)
    (x : f.specialFiber) :
    CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (f.cycleSpecialization r α) x =
      cycleSpecializationCoeff f r α x := sorry

/-- On the cycle of an integral closed subscheme of the generic fibre, specialization is
the degree-`r` associated cycle of the special fibre of its scheme-theoretic image. -/
theorem cycleSpecialization_point (r : ℕ) (z : f.genericFiber)
    (hz : f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))) z = r) :
    CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (f.cycleSpecialization r
          (CycleGroup.point
            (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r z hz)) =
      CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (IdealSheafData.associatedCycle (f.pointImageSpecial z)
          (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r) := sorry

end Scheme.Hom

namespace Scheme.Modules

/-- The degree-`r` associated cycle of a coherent module after pullback to a
scheme-theoretic fibre. -/
noncomputable def fiberAssociatedCycle {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsCoherent] [IsLocallyNoetherian X] (s : S) (r : ℕ)
    [IsLocallyNoetherian (f.fiber s)] :
    CycleGroup (f.fiber s) (f.fiberDimensionFunction s) r :=
  ⟨associatedCycle ((pullback (f.fiberι s)).obj F) (f.fiberDimensionFunction s) r,
    associatedCycle_mem_dimensionSubgroup
      ((pullback (f.fiberι s)).obj F) (f.fiberDimensionFunction s) r⟩

/-- Forgetting the grading of a fibre associated cycle recovers the associated algebraic
cycle of the pulled-back module. -/
theorem fiberAssociatedCycle_toAlgebraicCycle {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsCoherent] [IsLocallyNoetherian X] (s : S) (r : ℕ)
    [IsLocallyNoetherian (f.fiber s)] (x : f.fiber s) :
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r
        (fiberAssociatedCycle f F s r) x =
      associatedCycle ((pullback (f.fiberι s)).obj F)
        (f.fiberDimensionFunction s) r x := sorry

/-- Coefficients of a fibre associated cycle agree with the associated cycle of the
pulled-back module. -/
theorem fiberAssociatedCycle_apply {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsCoherent] [IsLocallyNoetherian X] (s : S) (r : ℕ)
    [IsLocallyNoetherian (f.fiber s)] (x : f.fiber s) :
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r
        (fiberAssociatedCycle f F s r) x =
      associatedCycle ((pullback (f.fiberι s)).obj F)
        (f.fiberDimensionFunction s) r x := sorry

end Scheme.Modules

end AlgebraicGeometry
