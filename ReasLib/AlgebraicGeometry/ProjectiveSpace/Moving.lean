module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearProjection.Intersection
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regular
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle.Variety
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionCycle

/-!
# Moving subvarieties by linear projection
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- For a regular closed variety `X` in projective space and a closed subvariety `Z` of
dimension strictly below that of `X`, there is an ambient subvariety whose intersection with
`X` contains `Z` with multiplicity one and whose residual components have no worse incidence
with any member of a prescribed finite family. -/
theorem existsMovingIntersectionCycle
    {I : Type u} [Finite I]
    (N n d d' : ℕ) (hV : Module.finrank k V = N + 1)
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (iX : X ⟶ Over.mk (ProjectiveSpace.VectorSpace.toSpec k V))
    [IsClosedImmersion iX.left]
    (hXdim : X.dimension = n) (hd : d < n) (hd' : d' < n)
    (Z : X.left.IdealSheafData)
    [Variety (Over.mk (Z.subschemeι ≫ X.hom))]
    (hZdim : dimension (Over.mk (Z.subschemeι ≫ X.hom)) = d)
    (T : I → X.left.IdealSheafData)
    [∀ i, Variety (Over.mk ((T i).subschemeι ≫ X.hom))]
    (hTdim : ∀ i,
      dimension (Over.mk ((T i).subschemeι ≫ X.hom)) = d') :
    ∃ C : (ProjectiveSpace.VectorSpace.scheme k V).IdealSheafData,
      Variety (Over.mk
        (C.subschemeι ≫ ProjectiveSpace.VectorSpace.toSpec k V)) ∧
      ∃ hproper : TopologicalSpace.Closeds.IntersectProperly C.support
          (iX.left.ker).support,
        ∃ (r : ℕ) (m : Fin r → ℕ)
            (Z' : Fin r → X.left.IdealSheafData),
          ∃ hZ'variety : ∀ j, Variety (Over.mk ((Z' j).subschemeι ≫ X.hom)),
          (∀ j, @dimension k _ (Over.mk ((Z' j).subschemeι ≫ X.hom))
            (hZ'variety j) = d) ∧
          (∀ j, Z' j ≠ Z) ∧
          C.intersectionCycle iX.left.ker hproper =
            CycleGroup.toAlgebraicCycle
              ((ProjectiveSpace.VectorSpace.toSpec k V).relativeDimensionFunction
                (fun _ ↦ 0)) (d : ℤ)
              (((Z.map (iX.left : X.left ⟶ ProjectiveSpace.VectorSpace.scheme k V)) :
                  (ProjectiveSpace.VectorSpace.scheme k V).IdealSheafData).associatedCycle
                ((ProjectiveSpace.VectorSpace.toSpec k V).relativeDimensionFunction
                  (fun _ ↦ 0)) (d : ℤ)) +
              ∑ j, m j • CycleGroup.toAlgebraicCycle
                ((ProjectiveSpace.VectorSpace.toSpec k V).relativeDimensionFunction
                  (fun _ ↦ 0)) (d : ℤ)
                ((((Z' j).map
                    (iX.left : X.left ⟶ ProjectiveSpace.VectorSpace.scheme k V)) :
                    (ProjectiveSpace.VectorSpace.scheme k V).IdealSheafData).associatedCycle
                    ((ProjectiveSpace.VectorSpace.toSpec k V).relativeDimensionFunction
                      (fun _ ↦ 0)) (d : ℤ)) ∧
          (∀ i j,
            topologicalKrullDim (((Z' j) ⊔ T i).subscheme) ≤
              topologicalKrullDim ((Z ⊔ T i).subscheme)) ∧
          ∀ i j, ¬ TopologicalSpace.Closeds.IntersectProperly Z.support (T i).support →
            topologicalKrullDim (((Z' j) ⊔ T i).subscheme) <
              topologicalKrullDim ((Z ⊔ T i).subscheme) := sorry

end AlgebraicGeometry.SchemeOverField
