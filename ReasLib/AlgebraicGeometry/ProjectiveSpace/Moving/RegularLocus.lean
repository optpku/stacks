module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Moving
public import ReasLib.AlgebraicGeometry.Scheme.Variety.RegularLocus
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionCycle.Open

@[expose] public section

open AlgebraicGeometry CategoryTheory Scheme Scheme.IdealSheafData TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- For a projective closure `X ⊆ ℙ(V)`, a subvariety of its regular locus and finitely many
subvarieties there, an ambient subvariety gives a proper intersection whose regular-locus
components have controlled incidence. -/
theorem existsMovingIntersectionCycleOnRegularLocus
    {I : Type u} [Finite I]
    (N n d d' : ℕ) (hV : Module.finrank k V = N + 1)
    (X : SchemeOverField k) [Variety X]
    (iX : X ⟶ Over.mk (ProjectiveSpace.VectorSpace.toSpec k V))
    [h_iX : IsClosedImmersion iX.left]
    (hXdim : X.dimension = n) (hd : d < n) (hd' : d' < n)
    (Z : IdealSheafData X.regularOpen.toScheme)
    [Variety (Over.mk (Z.subschemeι ≫ X.regularOpen.ι ≫ X.hom))]
    (hZdim : dimension (Over.mk (Z.subschemeι ≫ X.regularOpen.ι ≫ X.hom)) = d)
    (T : I → IdealSheafData X.regularOpen.toScheme)
    [∀ i, Variety (Over.mk ((T i).subschemeι ≫ X.regularOpen.ι ≫ X.hom))]
    (hTdim : ∀ i,
      dimension (Over.mk ((T i).subschemeι ≫ X.regularOpen.ι ≫ X.hom)) = d') :
    ∃ C : (ProjectiveSpace.VectorSpace.scheme k V).IdealSheafData,
      Variety (Over.mk
        (C.subschemeι ≫ ProjectiveSpace.VectorSpace.toSpec k V)) ∧
      ∃ hproper : TopologicalSpace.Closeds.IntersectProperly C.support iX.left.ker.support,
        ∃ (r : ℕ) (m : Fin r → ℤ)
            (Z' : Fin r → IdealSheafData X.regularOpen.toScheme),
          ∃ hZ'variety : ∀ j,
            Variety (Over.mk ((Z' j).subschemeι ≫ X.regularOpen.ι ≫ X.hom)),
          (∀ j, @dimension k _
            (Over.mk ((Z' j).subschemeι ≫ X.regularOpen.ι ≫ X.hom))
            (hZ'variety j) = d) ∧
          (∀ j, Z' j ≠ Z) ∧
          @intersectionCycleOnOpen X.left (ProjectiveSpace.VectorSpace.scheme k V) _ C
              (iX.left : X.left ⟶ ProjectiveSpace.VectorSpace.scheme k V)
              h_iX X.regularOpen hproper =
            CycleGroup.toAlgebraicCycle
              ((X.regularOpen.ι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0)) (d : ℤ)
              (Z.associatedCycle
                ((X.regularOpen.ι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0))
                (d : ℤ)) +
              ∑ j, m j • CycleGroup.toAlgebraicCycle
                ((X.regularOpen.ι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0)) (d : ℤ)
                ((Z' j).associatedCycle
                  ((X.regularOpen.ι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0))
                  (d : ℤ)) ∧
          (∀ i j,
            topologicalKrullDim (((Z' j) ⊔ T i).subscheme) ≤
              topologicalKrullDim ((Z ⊔ T i).subscheme)) ∧
          ∀ i j, ¬ TopologicalSpace.Closeds.IntersectProperly Z.support (T i).support →
            topologicalKrullDim (((Z' j) ⊔ T i).subscheme) <
              topologicalKrullDim ((Z ⊔ T i).subscheme) := sorry

end AlgebraicGeometry.SchemeOverField
