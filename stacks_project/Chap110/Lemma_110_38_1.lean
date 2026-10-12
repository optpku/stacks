/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteTypeFlatNotFinitePresentation
public import ReasLib.RingTheory.FiniteType.GeometricCounterexample
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 110.38.1 (1): there exists a flat finite type ring map with geometrically irreducible
complete intersection fibre rings which is not of finite presentation. -/
@[stacks 05LC]
#check (RingHom.FiniteTypeCounterexample.exists_irreducibleFibers :
  ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
    f.Flat ∧ f.FiniteType ∧ ¬f.FinitePresentation ∧
      GeometricallyIrreducible (Spec.map (CommRingCat.ofHom f)) ∧
        ∀ p : PrimeSpectrum R, RingHom.Fiber.IsGlobalCompleteIntersection f p.asIdeal)

/- Lemma 110.38.1 (2): there exists a flat finite type ring map with geometrically connected,
geometrically reduced, dimension 1, complete intersection fibre rings which is not of finite
presentation. -/
@[stacks 05LC]
#check (RingHom.FiniteTypeCounterexample.exists_connectedReducedFibers :
  ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
    f.Flat ∧ f.FiniteType ∧ ¬f.FinitePresentation ∧
      GeometricallyConnected (Spec.map (CommRingCat.ofHom f)) ∧
        GeometricallyReduced (Spec.map (CommRingCat.ofHom f)) ∧
          (∀ p : PrimeSpectrum R, ringKrullDim (f.Fiber p.asIdeal) = 1) ∧
            ∀ p : PrimeSpectrum R, RingHom.Fiber.IsGlobalCompleteIntersection f p.asIdeal)

/- Lemma 110.38.1 (3): there exists a proper flat morphism of schemes `X ⟶ S`, not of finite
presentation, each of whose fibres is isomorphic over the residue field to either `P¹` or the
vanishing locus of `X₁ * X₂` in `P²`. -/
@[stacks 05LC]
#check (AlgebraicGeometry.ProperFlatCounterexample.exists_nodalFibers :
  ∃ (X S : Scheme.{u}) (f : X ⟶ S),
    Flat f ∧ IsProper f ∧ ¬Scheme.Hom.FinitePresentation f ∧
      ∀ s : S,
        Nonempty
            (Over.mk (f.fiberToSpecResidueField s) ≅
              Over.mk (ProjectiveSpace.toBase 1 (Spec (S.residueField s)))) ∨
          ∃ Z : (ProjectiveSpace.scheme (S.residueField s) 2).IdealSheafData,
            ProjectiveSpace.ClosedSubscheme.HasHomogeneousEquation 2 Z
                (ProjectiveSpace.coordinate 2 1 * ProjectiveSpace.coordinate 2 2) ∧
              Nonempty
                (Over.mk (f.fiberToSpecResidueField s) ≅
                  Over.mk (Z.subschemeι ≫ ProjectiveSpace.toSpec (S.residueField s) 2)))

/- Lemma 110.38.1 (4): there exists a proper flat morphism of schemes `X ⟶ S`, not of finite
presentation, each of whose fibres is isomorphic over the residue field to either `P¹` or `P²`. -/
@[stacks 05LC]
#check (AlgebraicGeometry.ProperFlatCounterexample.exists_projectiveFibers :
  ∃ (X S : Scheme.{u}) (f : X ⟶ S),
    Flat f ∧ IsProper f ∧ ¬Scheme.Hom.FinitePresentation f ∧
      ∀ s : S,
        Nonempty
            (Over.mk (f.fiberToSpecResidueField s) ≅
              Over.mk (ProjectiveSpace.toBase 1 (Spec (S.residueField s)))) ∨
          Nonempty
            (Over.mk (f.fiberToSpecResidueField s) ≅
              Over.mk (ProjectiveSpace.toBase 2 (Spec (S.residueField s)))))
