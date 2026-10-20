module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Automorphism.SurfaceCounterexample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.SurfaceCounterexample

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex
open Scheme.IdealSheafData
open Scheme.Modules
open scoped AlgebraicGeometry

universe u

/- Remark 109.5.2 (1): the boundedness argument for automorphisms of curves fails for
moduli of surfaces: K3 surfaces over fields can have infinite discrete automorphism groups. -/
@[stacks 0DSR] #check (AlgebraicGeometry.SchemeOverField.exists_k3_infiniteDiscreteAutomorphismGroup :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (X : SchemeOverField k)
      (_ : Projective X.hom) (_ : IsProper X.hom) (_ : Smooth X.hom)
      (_ : IsIntegral X.left)
      (hdim : topologicalKrullDim X.left = 2)
      (hcanonical : Nonempty
        (dualizingModule X.hom ≅
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)))
      (hH1 : IsZero
        (Hom.cohomology X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)),
      Infinite (Aut X) ∧
        (∃ (G : SchemeOverField k)
          (_ : (AlgebraicGeometry.SchemeOverField.autFunctor X ⋙ forget GrpCat).RepresentableBy G),
          LocallyOfFiniteType G.hom ∧ DiscreteTopology G.left ∧
            topologicalKrullDim G.left = 0))

/- Remark 109.5.2 (2): on a projective surface over a field, the Hilbert polynomials of
two ample invertible sheaves do not give an a priori bound on that of their tensor product. -/
@[stacks 0DSR] #check (AlgebraicGeometry.SchemeOverField.not_exists_bound_tensorHilbertPolynomial_of_ample :
    ¬ ∃ B : (ℤ → ℤ) → (ℤ → ℤ) → (ℤ → ℤ),
      ∀ (k : Type u) [Field k] (S : SchemeOverField k)
        [Projective S.hom] [IsProper S.hom]
        (hSdim : topologicalKrullDim S.left = 2)
        (N L : S.left.Modules)
        [Invertible N] [Invertible L] [IsAmple N] [IsAmple L],
        ∀ n : ℤ,
          Hom.eulerCharacteristic S.hom (tensorPowerInt (N ⊗ L) n) ≤
            B (fun m ↦ Hom.eulerCharacteristic S.hom (tensorPowerInt N m))
              (fun m ↦ Hom.eulerCharacteristic S.hom (tensorPowerInt L m)) n)

/- Remark 109.5.2 (3): the intersection number of two ample effective Cartier divisors
on a projective surface has no upper bound in terms of their self-intersection numbers. -/
@[stacks 0DSR] #check (AlgebraicGeometry.SchemeOverField.not_exists_upperBound_intersectionNumber_of_selfNumbers :
    ¬ ∃ B : ℚ → ℚ → ℚ,
      ∀ (k : Type u) [Field k] (S : SchemeOverField k)
        [Projective S.hom] [IsProper S.hom]
        (hSdim : topologicalKrullDim S.left = 2)
        [HasExt
          (Sheaf (Opens.grothendieckTopology
            (⊥ : S.left.IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})]
        (H₁ H₂ : S.left.IdealSheafData)
        [IsEffectiveCartierDivisor H₁.subschemeι]
        [IsEffectiveCartierDivisor H₂.subschemeι]
        [IsAmple (associatedSheaf H₁)] [IsAmple (associatedSheaf H₂)],
        Intersection.number k S.hom ⊥
            (Intersection.topologicalKrullDim_bot_eq S.left hSdim)
            (associatedSheafPair H₁ H₂) ≤
          B (Intersection.selfNumber k S.hom ⊥
              (Intersection.topologicalKrullDim_bot_eq S.left hSdim)
              (associatedSheaf H₁))
            (Intersection.selfNumber k S.hom ⊥
              (Intersection.topologicalKrullDim_bot_eq S.left hSdim)
              (associatedSheaf H₂)))
