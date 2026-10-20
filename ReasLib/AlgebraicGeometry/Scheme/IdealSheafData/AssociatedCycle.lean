module

public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Noetherian.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.GenericPointLength
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension

/-!
# Associated cycles of closed subschemes

This file defines the multiplicities of the irreducible components of a closed subscheme and
the cycle obtained by summing the components of a fixed dimension with those multiplicities.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The multiplicity of a component of a closed subscheme is the length of its stalk as a
module over the ambient stalk. -/
noncomputable def componentMultiplicity [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (ξ : genericPoints Z.subscheme) : ℕ :=
  (Module.length (X.presheaf.stalk (Z.subschemeι ξ.1))
    ((ModuleCat.restrictScalars (Z.subschemeι.stalkMap ξ.1).hom).obj
      (ModuleCat.of (Z.subscheme.presheaf.stalk ξ.1)
        (Z.subscheme.presheaf.stalk ξ.1)))).toNat

/-- The natural-valued component multiplicity coerces to the corresponding ambient-stalk
module length. -/
theorem componentMultiplicity_eq_length [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (ξ : genericPoints Z.subscheme) :
    (componentMultiplicity Z ξ : ℕ∞) =
      Module.length (X.presheaf.stalk (Z.subschemeι ξ.1))
        ((ModuleCat.restrictScalars (Z.subschemeι.stalkMap ξ.1).hom).obj
          (ModuleCat.of (Z.subscheme.presheaf.stalk ξ.1)
            (Z.subscheme.presheaf.stalk ξ.1))) := sorry

/-- The singleton algebraic cycle of a component, weighted by its multiplicity in the closed
subscheme. -/
noncomputable def componentCycle [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (ξ : genericPoints Z.subscheme) : AlgebraicCycle X ℤ :=
  @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
    (Z.subschemeι ξ.1) (componentMultiplicity Z ξ : ℤ)

/-- The component cycle is supported at its ambient generic point and has the component
multiplicity there. -/
theorem componentCycle_apply [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (ξ : genericPoints Z.subscheme) (x : X) :
    componentCycle Z ξ x =
      @ite ℤ (x = Z.subschemeι ξ.1) (Classical.propDecidable _)
        (componentMultiplicity Z ξ : ℤ) 0 := sorry

/-- The pointwise sum of the dimension-`k` component cycles has locally finite support. -/
theorem associatedCycleLocallyFiniteSupport [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (d : X → ℤ) (k : ℤ) :
    LocallyFiniteSupport (fun x : X ↦
      ∑ᶠ ξ : genericPoints Z.subscheme,
        @ite ℤ (d (Z.subschemeι ξ.1) = k) (Classical.propDecidable _)
          (componentCycle Z ξ x) 0) := sorry

/-- The underlying associated cycle is supported in dimension `k`. -/
theorem associatedCycle_mem_dimensionSubgroup [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (d : X → ℤ) (k : ℤ) :
    ({ toFun := fun x ↦ ∑ᶠ ξ : genericPoints Z.subscheme,
          @ite ℤ (d (Z.subschemeι ξ.1) = k) (Classical.propDecidable _)
            (componentCycle Z ξ x) 0
       supportWithinDomain' := Set.subset_univ _
       supportLocallyFiniteWithinDomain' :=
         fun x _ ↦ associatedCycleLocallyFiniteSupport Z d k x } :
      AlgebraicCycle X ℤ) ∈ AlgebraicCycle.dimensionSubgroup d k := sorry

/-- The multiplicity-weighted degree-`k` cycle associated to a closed subscheme. -/
noncomputable def associatedCycle [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (d : X → ℤ) (k : ℤ) : AlgebraicGeometry.CycleGroup X d k :=
  ⟨{ toFun := fun x ↦ ∑ᶠ ξ : genericPoints Z.subscheme,
        @ite ℤ (d (Z.subschemeι ξ.1) = k) (Classical.propDecidable _)
          (componentCycle Z ξ x) 0
     supportWithinDomain' := Set.subset_univ _
     supportLocallyFiniteWithinDomain' :=
       fun x _ ↦ associatedCycleLocallyFiniteSupport Z d k x },
    associatedCycle_mem_dimensionSubgroup Z d k⟩

/-- Coefficients of the associated cycle are the pointwise finite sum of the multiplicity-weighted
dimension-`k` component cycles. -/
theorem associatedCycle_apply [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (d : X → ℤ) (k : ℤ) (x : X) :
    (associatedCycle Z d k : AlgebraicCycle X ℤ) x =
      ∑ᶠ ξ : genericPoints Z.subscheme,
        @ite ℤ (d (Z.subschemeι ξ.1) = k) (Classical.propDecidable _)
          (componentCycle Z ξ x) 0 := sorry

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

/-- The degree-`k` cycle of a closed subscheme, measured using the relative dimension function
of a locally finite type morphism. -/
noncomputable def closedSubschemeCycle
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData) (k : ℤ)
    (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)) :
    AlgebraicGeometry.CycleGroup X (f.relativeDimensionFunction δ) k :=
  @IdealSheafData.associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian f) Z
    (f.relativeDimensionFunction δ) k

/-- Coefficients of the closed-subscheme cycle are the multiplicity-weighted sum over its
dimension-`k` generic points. -/
theorem closedSubschemeCycle_apply
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData) (k : ℤ)
    (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)) (x : X) :
    (closedSubschemeCycle f δ Z k hZ : AlgebraicCycle X ℤ) x =
      ∑ᶠ ξ : genericPoints Z.subscheme,
        @ite ℤ (f.relativeDimensionFunction δ (Z.subschemeι ξ.1) = k)
          (Classical.propDecidable _)
          (@IdealSheafData.componentCycle X
            (LocallyOfFiniteType.isLocallyNoetherian f) Z ξ x) 0 := sorry

end AlgebraicGeometry.Scheme.Hom
