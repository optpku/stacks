module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionCycle
public import stacks_project.Chap43.Lemma_43_14_3_IntersectionMultiplicity

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/- The expected-dimension construction is provided by the reusable intersection-cycle API. -/
#check (AlgebraicGeometry.Scheme.IdealSheafData.expectedIntersectionDimension :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    (V W : X.left.IdealSheafData) [IsIntegral V.subscheme] [IsIntegral W.subscheme], ℤ)

/- The expected-dimension computation law is provided by the reusable intersection-cycle API. -/
#check (AlgebraicGeometry.Scheme.IdealSheafData.expectedIntersectionDimension_def :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    (V W : X.left.IdealSheafData) [IsIntegral V.subscheme] [IsIntegral W.subscheme],
    expectedIntersectionDimension X V W =
      X.hom.relativeDimensionFunction (fun _ ↦ 0)
          (V.subschemeι (genericPoint V.subscheme)) +
        X.hom.relativeDimensionFunction (fun _ ↦ 0)
          (W.subschemeι (genericPoint W.subscheme)) -
        X.hom.relativeDimensionFunction (fun _ ↦ 0) (genericPoint X.left))

/- Local finiteness of intersection-cycle coefficients is provided by the reusable API. -/
#check (AlgebraicGeometry.Scheme.IdealSheafData.intersectionCycleLocallyFiniteSupport :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
    (V W : X.IdealSheafData) (hproper : V.IntersectsProperly W),
    LocallyFiniteSupport (fun x : X ↦
      ∑ᶠ Z : irreducibleComponents (V ⊔ W).subscheme,
        @ite ℤ (x = (V ⊔ W).subschemeι (genericPoints.ofComponent Z).1)
          (Classical.propDecidable _)
          (V.intersectionMultiplicity W (genericPoints.ofComponent Z)) 0))

/- The intersection-cycle construction is provided by the reusable API. -/
#check (AlgebraicGeometry.Scheme.IdealSheafData.intersectionCycle :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
    (V W : X.IdealSheafData) (_ : V.IntersectsProperly W), AlgebraicCycle X ℤ)

/- The intersection-cycle coefficient formula is provided by the reusable API. -/
#check (AlgebraicGeometry.Scheme.IdealSheafData.intersectionCycle_apply :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
    (V W : X.IdealSheafData) (hproper : V.IntersectsProperly W) (x : X),
    intersectionCycle V W hproper x =
      ∑ᶠ Z : irreducibleComponents (V ⊔ W).subscheme,
        @ite ℤ (x = (V ⊔ W).subschemeι (genericPoints.ofComponent Z).1)
          (Classical.propDecidable _)
          (V.intersectionMultiplicity W (genericPoints.ofComponent Z)) 0)

end AlgebraicGeometry.Scheme.IdealSheafData
