module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Whole
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Failure of uniform bounds for ample sheaves on surfaces
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.IdealSheafData
open Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

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

/-- There is no uniform pointwise upper bound for the Hilbert polynomial of the tensor
product of two ample invertible modules on a projective surface over a field determined by
the Hilbert polynomials of the two factors. -/
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

/-- The mixed intersection number of two ample effective Cartier divisors on a projective
surface has no uniform upper bound determined by their self-intersection numbers. -/
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
