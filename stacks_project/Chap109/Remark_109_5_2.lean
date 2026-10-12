/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Whole
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Automorphism

/-!
# Automorphism groups of surfaces

The boundedness argument for the diagonal of `Curves` does not extend to
moduli of surfaces: some K3 surfaces have infinite discrete automorphism
groups, because Hilbert polynomials of ample invertibles are not uniformly
bounded under tensor product.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex
open Scheme.IdealSheafData
open Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Integral tensor powers of invertible scheme modules remain invertible. -/
instance instInvertible_tensorPowerInt
    {X : Scheme.{u}} (L : X.Modules) [Invertible L] (n : ℤ) :
    Invertible (tensorPowerInt L n) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The pair of invertible sheaves associated to two effective Cartier divisors. -/
noncomputable def associatedSheafPair
    {X : Scheme.{u}} (H₁ H₂ : X.IdealSheafData)
    [IsEffectiveCartierDivisor H₁.subschemeι]
    [IsEffectiveCartierDivisor H₂.subschemeι] :
    Fin 2 → X.Modules :=
  ![associatedSheaf H₁, associatedSheaf H₂]

/-- `associatedSheafPair` is the `Fin 2`-family of associated sheaves. -/
theorem associatedSheafPair_def
    {X : Scheme.{u}} (H₁ H₂ : X.IdealSheafData)
    [IsEffectiveCartierDivisor H₁.subschemeι]
    [IsEffectiveCartierDivisor H₂.subschemeι] :
    associatedSheafPair H₁ H₂ = ![associatedSheaf H₁, associatedSheaf H₂] := sorry

/-- Each factor of `associatedSheafPair` is invertible. -/
instance instInvertible_associatedSheafPair
    {X : Scheme.{u}} (H₁ H₂ : X.IdealSheafData)
    [IsEffectiveCartierDivisor H₁.subschemeι]
    [IsEffectiveCartierDivisor H₂.subschemeι] :
    ∀ j : Fin 2, Invertible (associatedSheafPair H₁ H₂ j) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.SchemeOverField

/-- Remark 109.5.2 (1): the analogue of Lemma 109.5.1 fails for surfaces, because
some K3 surfaces over fields have infinite discrete automorphism groups. -/
@[stacks 0DSR]
theorem exists_k3_infiniteDiscreteAutomorphismGroup :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (X : SchemeOverField k)
      (_ : Projective X.hom) (_ : IsProper X.hom) (_ : Smooth X.hom)
      (hdim : topologicalKrullDim X.left = 2)
      (hcanonical : Nonempty
        (dualizingModule X.hom ≅
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)))
      (hH1 : IsZero
        (Hom.cohomology X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)),
      Infinite (Aut X) ∧
        ∀ (G : SchemeOverField k),
          (autFunctor X ⋙ forget GrpCat).RepresentableBy G →
            topologicalKrullDim G.left = 0 := sorry

/-- Remark 109.5.2 (2): on a projective surface `S` over a field, ample invertible
sheaves `N` and `L` with Hilbert polynomials `Q` and `P` give no a priori bound
on the Hilbert polynomial of `N ⊗ L`, i.e. on `n ↦ Hom.eulerCharacteristic`
of `tensorPowerInt (N ⊗ L) n`. -/
@[stacks 0DSR]
theorem not_exists_bound_tensorHilbertPolynomial_of_ample :
    ¬ ∃ B : (ℤ → ℤ) → (ℤ → ℤ) → (ℤ → ℤ),
      ∀ (k : Type u) [Field k] (S : SchemeOverField k)
        [Projective S.hom] [IsProper S.hom]
        (hSdim : topologicalKrullDim S.left = 2)
        (N L : S.left.Modules)
        [Invertible N] [Invertible L] [IsAmple N] [IsAmple L],
        ∀ n : ℤ,
          Hom.eulerCharacteristic S.hom (tensorPowerInt (N ⊗ L) n) ≤
            B (fun m ↦ Hom.eulerCharacteristic S.hom (tensorPowerInt N m))
              (fun m ↦ Hom.eulerCharacteristic S.hom (tensorPowerInt L m)) n := sorry

/-- Remark 109.5.2 (3): if `H₁`, `H₂` are ample effective Cartier divisors on a
projective surface `S`, there is no upper bound on the intersection number
`H₁ · H₂` in terms of `H₁ · H₁` and `H₂ · H₂`. -/
@[stacks 0DSR]
theorem not_exists_upperBound_intersectionNumber_of_selfNumbers :
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
              (associatedSheaf H₂)) := sorry

end AlgebraicGeometry.SchemeOverField
