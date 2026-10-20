module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Moving
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/- Lemma 43.24.1: a closed subvariety of a nonsingular projective variety is a
multiplicity-one component of a proper intersection whose residual components
have improved incidence with a prescribed finite family. -/
@[stacks 0B0E] #check
  (AlgebraicGeometry.SchemeOverField.existsMovingIntersectionCycle :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      {I : Type u} [Finite I]
      (N n d d' : ℕ) (hV : Module.finrank k V = N + 1)
      (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      (iX : X ⟶ Over.mk (ProjectiveSpace.VectorSpace.toSpec k V))
      [IsClosedImmersion iX.left]
      (hXdim : X.dimension = n) (hd : d < n) (hd' : d' < n)
      (Z : X.left.IdealSheafData)
      [Variety (Over.mk (Z.subschemeι ≫ X.hom))]
      (hZdim : SchemeOverField.dimension
        (Over.mk (Z.subschemeι ≫ X.hom)) = d)
      (T : I → X.left.IdealSheafData)
      [∀ i, Variety (Over.mk ((T i).subschemeι ≫ X.hom))]
      (hTdim : ∀ i, SchemeOverField.dimension
        (Over.mk ((T i).subschemeι ≫ X.hom)) = d'),
      ∃ C : (ProjectiveSpace.VectorSpace.scheme k V).IdealSheafData,
        Variety (Over.mk
          (C.subschemeι ≫ ProjectiveSpace.VectorSpace.toSpec k V)) ∧
        ∃ hproper : TopologicalSpace.Closeds.IntersectProperly C.support
            (iX.left.ker).support,
          ∃ (r : ℕ) (m : Fin r → ℕ)
              (Z' : Fin r → X.left.IdealSheafData),
            ∃ hZ'variety : ∀ j,
                Variety (Over.mk ((Z' j).subschemeι ≫ X.hom)),
            (∀ j, @SchemeOverField.dimension k _
              (Over.mk ((Z' j).subschemeι ≫ X.hom)) (hZ'variety j) = d) ∧
            (∀ j, Z' j ≠ Z) ∧
            C.intersectionCycle iX.left.ker hproper =
              CycleGroup.toAlgebraicCycle
                ((ProjectiveSpace.VectorSpace.toSpec k V).relativeDimensionFunction
                  (fun _ ↦ 0)) (d : ℤ)
                (((Z.map
                    (iX.left : X.left ⟶ ProjectiveSpace.VectorSpace.scheme k V)) :
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
            ∀ i j,
              ¬ TopologicalSpace.Closeds.IntersectProperly Z.support (T i).support →
                topologicalKrullDim (((Z' j) ⊔ T i).subscheme) <
                  topologicalKrullDim ((Z ⊔ T i).subscheme))
