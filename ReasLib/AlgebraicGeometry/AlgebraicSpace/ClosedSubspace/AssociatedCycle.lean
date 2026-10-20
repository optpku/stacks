module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.WithBotTop
public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.IrreducibleComponents

/-!
# Associated cycles of closed subspaces of algebraic spaces

This file defines the multiplicity of an irreducible component of a closed subspace
and the multiplicity-weighted `k`-cycle associated to that subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The natural truncation of the supremum of geometric-stalk lengths of `𝒪_Y`
over a component's generic point. For a decent closed subspace of a locally
Noetherian space, this is its finite positive component length. -/
noncomputable def componentMultiplicity [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) (η : genericPoints Y.X) : ℕ :=
  (⨆ p : {p : GeometricPoint Y.X // p.liesOver η.1},
      Modules.lengthAtGeometricPoint
        (SheafOfModules.unit (structureSheaf Y.X) : Y.X.Modules) p.1).toNat

/-- On a decent closed subspace of a locally Noetherian space, component
multiplicity coerces to the length of `𝒪_Y` at every geometric point over its
generic point. -/
theorem componentMultiplicity_eq_length [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X)
    (xbar : GeometricPoint Y.X) (hx : xbar.liesOver η.1) :
    (componentMultiplicity Y η : ℕ∞) =
      Modules.lengthAtGeometricPoint
        (SheafOfModules.unit (structureSheaf Y.X) : Y.X.Modules) xbar :=
  sorry

/-- On a decent closed subspace of a locally Noetherian space, component
multiplicity is the length of `𝒪_Y` at its generic point in the sense of `hasLengthAt`. -/
theorem hasLengthAt_componentMultiplicity [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X) :
    Modules.hasLengthAt (SheafOfModules.unit (structureSheaf Y.X) : Y.X.Modules) η.1
      (componentMultiplicity Y η) :=
  sorry

/-- Every component of a decent closed subspace of a locally Noetherian space
has positive multiplicity. -/
theorem componentMultiplicity_pos [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X) :
    0 < componentMultiplicity Y η :=
  sorry

/-- The singleton cycle of a component, weighted by its multiplicity in the closed
subspace, supported at the image of the generic point in `|X|`. -/
noncomputable def componentCycle [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) (η : genericPoints Y.X) :
    Function.locallyFinsupp (Points X) ℤ :=
  @Function.locallyFinsuppWithin.single (Points X) _ ℤ (Classical.decEq _) _
    (Points.map Y.ι η.1) (componentMultiplicity Y η : ℤ)

/-- The component cycle is supported at the image of its generic point and has the
component multiplicity there. -/
theorem componentCycle_apply [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) (η : genericPoints Y.X) (x : Points X) :
    componentCycle Y η x =
      @ite ℤ (x = Points.map Y.ι η.1) (Classical.propDecidable _)
        (componentMultiplicity Y η : ℤ) 0 :=
  sorry

/-- The pointwise sum of the dimension-`k` component cycles has locally finite
support. -/
theorem associatedCycle_locallyFiniteSupport [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) (d : Points X → ℤ) (k : ℤ) :
    LocallyFiniteSupport fun x : Points X ↦
      ∑ᶠ η : genericPoints Y.X,
        @ite ℤ (d (Points.map Y.ι η.1) = k) (Classical.propDecidable _)
          (componentCycle Y η x) 0 :=
  sorry

/-- The multiplicity-weighted degree-`k` cycle associated to a closed subspace. -/
noncomputable def associatedCycle [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) (d : Points X → ℤ) (k : ℤ) :
    Function.locallyFinsupp (Points X) ℤ where
  toFun := fun x ↦
    ∑ᶠ η : genericPoints Y.X,
      @ite ℤ (d (Points.map Y.ι η.1) = k) (Classical.propDecidable _)
        (componentCycle Y η x) 0
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    associatedCycle_locallyFiniteSupport Y d k x

/-- Coefficients of the associated cycle are the pointwise finite sum of the
multiplicity-weighted dimension-`k` component cycles. -/
theorem associatedCycle_apply [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) (d : Points X → ℤ) (k : ℤ) (x : Points X) :
    associatedCycle Y d k x =
      ∑ᶠ η : genericPoints Y.X,
        @ite ℤ (d (Points.map Y.ι η.1) = k) (Classical.propDecidable _)
          (componentCycle Y η x) 0 :=
  sorry

/-- Off the `δ`-dimension-`k` locus, the associated cycle coefficient vanishes. -/
theorem associatedCycle_eq_zero_of_dimension_ne [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) (d : Points X → ℤ) (k : ℤ) {x : Points X}
    (hx : d x ≠ k) : associatedCycle Y d k x = 0 :=
  sorry

end ClosedSubspace

namespace Hom

/-- The degree-`k` cycle of a closed subspace, measured using the relative dimension
function of a good morphism. -/
noncomputable def closedSubspaceCycle {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ)
    (hY : (closedSubspaceDeltaDimension f) δ Y ≤ (k : EInt)) :
    Function.locallyFinsupp (Points X) ℤ :=
  @ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Y
    ((relativeDimensionFunction f) δ) k

/-- The closed-subspace cycle is the associated cycle for the relative dimension
function. -/
theorem closedSubspaceCycle_eq_associatedCycle {S : Scheme.{u}}
    {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ)
    (hY : (closedSubspaceDeltaDimension f) δ Y ≤ (k : EInt)) :
    closedSubspaceCycle f δ Y k hY =
      @ClosedSubspace.associatedCycle S X
        (LocallyOfFiniteType.isLocallyNoetherian f) Y
        ((relativeDimensionFunction f) δ) k :=
  sorry

/-- Coefficients of the closed-subspace cycle are the multiplicity-weighted sum over
its dimension-`k` generic points. -/
theorem closedSubspaceCycle_apply {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ)
    (hY : (closedSubspaceDeltaDimension f) δ Y ≤ (k : EInt)) (x : Points X) :
    closedSubspaceCycle f δ Y k hY x =
      ∑ᶠ η : genericPoints Y.X,
        @ite ℤ ((relativeDimensionFunction f) δ (Points.map Y.ι η.1) = k)
          (Classical.propDecidable _)
          (@ClosedSubspace.componentCycle S X
            (LocallyOfFiniteType.isLocallyNoetherian f) Y η x) 0 :=
  sorry

/-- The associated closed-subspace cycle belongs to the group of cycles of its
specified relative dimension. -/
theorem closedSubspaceCycle_mem_cycleGroup {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ)
    (hY : (closedSubspaceDeltaDimension f) δ Y ≤ (k : EInt)) :
    closedSubspaceCycle f δ Y k hY ∈ Hom.cycleGroup f δ k :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
