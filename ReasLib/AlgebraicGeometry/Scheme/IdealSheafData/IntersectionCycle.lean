/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity

/-!
# Intersection cycles of closed subschemes

This module defines the expected dimension and the cycle obtained from the Serre
intersection multiplicities of two properly intersecting closed subschemes.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The expected dimension of the intersection of two integral closed subschemes of a
variety, measured by the relative dimension function over the base field. -/
noncomputable def expectedIntersectionDimension {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] (V W : X.left.IdealSheafData)
    [IsIntegral V.subscheme] [IsIntegral W.subscheme] : ℤ :=
  X.hom.relativeDimensionFunction (fun _ ↦ 0)
      (V.subschemeι (genericPoint V.subscheme)) +
    X.hom.relativeDimensionFunction (fun _ ↦ 0)
      (W.subschemeι (genericPoint W.subscheme)) -
    X.hom.relativeDimensionFunction (fun _ ↦ 0) (genericPoint X.left)

/-- The expected intersection dimension is the sum of the dimensions of the two closed
subvarieties minus the dimension of the ambient variety. -/
theorem expectedIntersectionDimension_def {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] (V W : X.left.IdealSheafData)
    [IsIntegral V.subscheme] [IsIntegral W.subscheme] :
    expectedIntersectionDimension X V W =
      X.hom.relativeDimensionFunction (fun _ ↦ 0)
          (V.subschemeι (genericPoint V.subscheme)) +
        X.hom.relativeDimensionFunction (fun _ ↦ 0)
          (W.subschemeι (genericPoint W.subscheme)) -
        X.hom.relativeDimensionFunction (fun _ ↦ 0) (genericPoint X.left) := sorry

/-- The component-weighted Serre intersection multiplicities have locally finite support
on the ambient scheme. -/
theorem intersectionCycleLocallyFiniteSupport [IsLocallyNoetherian X]
    (V W : X.IdealSheafData) (hproper : Closeds.IntersectProperly V.support W.support) :
    LocallyFiniteSupport (fun x : X ↦
      ∑ᶠ Z : irreducibleComponents (V ⊔ W).subscheme,
        @ite ℤ (x = (V ⊔ W).subschemeι (genericPoints.ofComponent Z).1)
          (Classical.propDecidable _)
          (V.intersectionMultiplicity W (genericPoints.ofComponent Z)) 0) := sorry

/-- The intersection cycle of two properly intersecting closed subschemes is the explicit
sum of their Serre multiplicities at the generic points of the intersection components. -/
noncomputable def intersectionCycle [IsLocallyNoetherian X]
    (V W : X.IdealSheafData) (hproper : Closeds.IntersectProperly V.support W.support) :
    AlgebraicCycle X ℤ where
  toFun := fun x ↦
    ∑ᶠ Z : irreducibleComponents (V ⊔ W).subscheme,
      @ite ℤ (x = (V ⊔ W).subschemeι (genericPoints.ofComponent Z).1)
        (Classical.propDecidable _)
        (V.intersectionMultiplicity W (genericPoints.ofComponent Z)) 0
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    intersectionCycleLocallyFiniteSupport V W hproper x

/-- The coefficient function of the intersection cycle is the pointwise sum of the Serre
multiplicities of the intersection components with that ambient generic point. -/
theorem intersectionCycle_apply [IsLocallyNoetherian X]
    (V W : X.IdealSheafData) (hproper : Closeds.IntersectProperly V.support W.support)
    (x : X) :
    intersectionCycle V W hproper x =
      ∑ᶠ Z : irreducibleComponents (V ⊔ W).subscheme,
        @ite ℤ (x = (V ⊔ W).subschemeι (genericPoints.ofComponent Z).1)
          (Classical.propDecidable _)
          (V.intersectionMultiplicity W (genericPoints.ofComponent Z)) 0 := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
