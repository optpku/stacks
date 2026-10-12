/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.StructureSheafCycle

open TopologicalSpace

noncomputable section

universe u

/- The reusable coherent-module associated-cycle API. -/
#check (AlgebraicGeometry.Scheme.Modules.associatedCycleLocallyFiniteSupport :
  {X : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsLocallyNoetherian X] →
    (F : X.Modules) → [F.IsCoherent] → (d : X → ℤ) → (k : ℤ) →
      LocallyFiniteSupport (fun x : X ↦
        @ite ℤ
          (x ∈ X.minimalSpecializationPoints
            (AlgebraicGeometry.Scheme.Modules.moduleSupport F) ∧ d x = k)
          (Classical.propDecidable _)
          ((Module.length (X.presheaf.stalk x)
            (AlgebraicGeometry.RingedSpace.stalkModuleCat F x)).toNat : ℤ)
          0))

#check (AlgebraicGeometry.Scheme.Modules.associatedCycle :
  {X : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsLocallyNoetherian X] →
    (F : X.Modules) → [F.IsCoherent] → (d : X → ℤ) → (k : ℤ) →
      AlgebraicGeometry.AlgebraicCycle X ℤ)

#check (AlgebraicGeometry.Scheme.Modules.associatedCycle_apply :
  {X : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsLocallyNoetherian X] →
    (F : X.Modules) → [F.IsCoherent] → (d : X → ℤ) → (k : ℤ) → (x : X) →
      AlgebraicGeometry.Scheme.Modules.associatedCycle F d k x =
        @ite ℤ
          (x ∈ X.minimalSpecializationPoints
            (AlgebraicGeometry.Scheme.Modules.moduleSupport F) ∧ d x = k)
          (Classical.propDecidable _)
          ((Module.length (X.presheaf.stalk x)
            (AlgebraicGeometry.RingedSpace.stalkModuleCat F x)).toNat : ℤ)
          0)

#check (AlgebraicGeometry.Scheme.Modules.associatedCycle_mem_dimensionSubgroup :
  {X : AlgebraicGeometry.Scheme.{u}} → [AlgebraicGeometry.IsLocallyNoetherian X] →
    (F : X.Modules) → [F.IsCoherent] → (d : X → ℤ) → (k : ℤ) →
      AlgebraicGeometry.Scheme.Modules.associatedCycle F d k ∈
        AlgebraicGeometry.AlgebraicCycle.dimensionSubgroup d k)

/- The support API for the pushed-forward structure sheaf of a closed subscheme. -/
#check (AlgebraicGeometry.closedSubschemeStructureSheafOn_support :
  {X : AlgebraicGeometry.Scheme.{u}} → (Z : X.IdealSheafData) →
    AlgebraicGeometry.RingedSpace.moduleSupport
        (AlgebraicGeometry.closedSubschemeStructureSheafOn Z) =
      (Z.support : Set X))
