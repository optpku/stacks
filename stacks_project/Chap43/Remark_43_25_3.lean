module

public import ReasLib.AlgebraicGeometry.ChowGroup.Moving.QuasiProjective
public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.QuasiProjective
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Moving.RegularLocus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Scheme Scheme.IdealSheafData TopologicalSpace
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

/- Remark 43.25.3 (1): on a nonsingular quasi-projective variety, every `r`-cycle is
rationally equivalent to an `r`-cycle intersecting a prescribed `s`-cycle properly. -/
@[stacks 0B61] #check (AlgebraicGeometry.CycleGroup.existsRationallyEquivalentIntersectProperly_of_quasiProjective :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [QuasiProjectiveVariety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (β : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s),
    ∃ α' : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r,
      RationalEquivalence.RationallyEquivalent
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α' α ∧
        AlgebraicCycle.IntersectProperly
          (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α')
          (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s β))

/- Remark 43.25.3 (2): on a nonsingular quasi-projective variety over an algebraically closed
field, the proper intersection of a cycle rationally equivalent to zero with another cycle is
rationally equivalent to zero. -/
@[stacks 0B61] #check (AlgebraicGeometry.CycleGroup.intersection_rationallyEquivalent_zero_of_quasiProjective :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [QuasiProjectiveVariety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (β : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α)
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s β))
    (hα : RationalEquivalence.RationallyEquivalent
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r α 0),
    RationalEquivalence.RationallyEquivalent
      (X.hom.relativeDimensionFunction (fun _ ↦ 0))
      (r + s - (X.dimension : ℤ))
      (CycleGroup.intersection X r s α β hproper) 0)

/- Remark 43.25.3 (3): for a projective closure `X ⊆ ℙ(V)`, a dimension-`d`
subvariety `Z` of `X.regularOpen`, and finitely many dimension-`d'` subvarieties `T i`
there, an ambient subvariety `C` intersects `X` properly and restricts on the regular locus
to `[Z]` plus a finite integral combination of dimension-`d` subvarieties. -/
@[stacks 0B61] #check (AlgebraicGeometry.SchemeOverField.existsMovingIntersectionCycleOnRegularLocus :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {I : Type u} [Finite I]
    (N n d d' : ℕ) (hV : Module.finrank k V = N + 1)
    (X : SchemeOverField k) [Variety X]
    (iX : X ⟶ Over.mk (ProjectiveSpace.VectorSpace.toSpec k V))
    [h_iX : IsClosedImmersion iX.left]
    (hXdim : X.dimension = n) (hd : d < n) (hd' : d' < n)
    (Z : IdealSheafData X.regularOpen.toScheme)
    [Variety (Over.mk (Z.subschemeι ≫ X.regularOpen.ι ≫ X.hom))]
    (hZdim : SchemeOverField.dimension (Over.mk (Z.subschemeι ≫ X.regularOpen.ι ≫ X.hom)) = d)
    (T : I → IdealSheafData X.regularOpen.toScheme)
    [∀ i, Variety (Over.mk ((T i).subschemeι ≫ X.regularOpen.ι ≫ X.hom))]
    (hTdim : ∀ i, SchemeOverField.dimension (Over.mk ((T i).subschemeι ≫ X.regularOpen.ι ≫ X.hom)) = d'),
    ∃ C : (ProjectiveSpace.VectorSpace.scheme k V).IdealSheafData,
      Variety (Over.mk (C.subschemeι ≫ ProjectiveSpace.VectorSpace.toSpec k V)) ∧
      ∃ hproper : Closeds.IntersectProperly C.support iX.left.ker.support,
        ∃ (r : ℕ) (m : Fin r → ℤ) (Z' : Fin r → IdealSheafData X.regularOpen.toScheme),
          ∃ hZ'variety : ∀ j,
            Variety (Over.mk ((Z' j).subschemeι ≫ X.regularOpen.ι ≫ X.hom)),
          (∀ j, @SchemeOverField.dimension k _
            (Over.mk ((Z' j).subschemeι ≫ X.regularOpen.ι ≫ X.hom))
            (hZ'variety j) = d) ∧
          (∀ j, Z' j ≠ Z) ∧
          @Scheme.IdealSheafData.intersectionCycleOnOpen X.left
              (ProjectiveSpace.VectorSpace.scheme k V) _ C
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
          ∀ i j, ¬ Closeds.IntersectProperly Z.support (T i).support →
            topologicalKrullDim (((Z' j) ⊔ T i).subscheme) <
              topologicalKrullDim ((Z ⊔ T i).subscheme))
