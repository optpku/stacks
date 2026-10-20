module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Prime.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.OfGlobal
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopCat.Presheaf
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]

/-- The sheaf associated to an effective Cartier divisor is invertible. -/
instance instInvertibleAssociatedSheaf (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    Modules.Invertible (IdealSheafData.associatedSheaf D) := sorry

/-- The canonical section of an effective Cartier divisor remains nonzero as a meromorphic
section. -/
theorem canonicalSection_toMeromorphicSection_ne_zero (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    Modules.toMeromorphicSection (IdealSheafData.associatedSheaf D)
      (IdealSheafData.canonicalSection D) ≠ 0 := sorry

open Classical in
/-- The Weil divisor associated to an effective Cartier divisor on a Noetherian integral
scheme. -/
def weilDivisor_ofEffectiveCartier (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] : WeilDivisor X :=
  let s := Modules.toMeromorphicSection (IdealSheafData.associatedSheaf D)
    (IdealSheafData.canonicalSection D)
  if h : s = 0 then 0
  else nonzeroMeromorphicSectionWeilDivisor X (IdealSheafData.associatedSheaf D) s h

/-- If the canonical meromorphic section is nonzero, the associated Weil divisor is the
meromorphic-section Weil divisor. -/
theorem weilDivisor_ofEffectiveCartier_eq_of_ne_zero (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (h : Modules.toMeromorphicSection (IdealSheafData.associatedSheaf D)
      (IdealSheafData.canonicalSection D) ≠ 0) :
    weilDivisor_ofEffectiveCartier D =
      nonzeroMeromorphicSectionWeilDivisor X (IdealSheafData.associatedSheaf D)
        (Modules.toMeromorphicSection (IdealSheafData.associatedSheaf D)
          (IdealSheafData.canonicalSection D)) h := sorry

/-- The associated Weil coefficient vanishes when the generic point of the prime divisor does
not lie on the effective Cartier divisor. -/
theorem weilDivisor_ofEffectiveCartier_coeff_eq_zero_of_not_mem (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (Z : PrimeDivisor X)
    (hZ : Z.genericPoint ∉ D.support) :
    (weilDivisor_ofEffectiveCartier D).coeff Z = 0 := sorry

/-- On a local nonzerodivisor equation, the associated Weil coefficient is the order of
vanishing of that equation in the function field. -/
theorem effectiveCartierOrder_spec (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (Z : PrimeDivisor X)
    (U : X.affineOpens) (f : Γ(X, U))
    (hξ : Z.genericPoint ∈ (U : X.Opens))
    (hf : f ∈ nonZeroDivisors (Γ(X, U)))
    (hgen : D.ideal U = Ideal.span ({f} : Set (Γ(X, U)))) :
    (weilDivisor_ofEffectiveCartier D).coeff Z =
      X.ord (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField
        (X.presheaf.germ (U : X.Opens) Z.genericPoint hξ f)) Z.genericPoint := sorry

/-- On a local nonzerodivisor equation, the associated Weil coefficient is the length of the
quotient of the local ring of `Z` by that equation. -/
theorem effectiveCartierOrder_eq_length (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (Z : PrimeDivisor X)
    (U : X.affineOpens) (f : Γ(X, U))
    (hξ : Z.genericPoint ∈ (U : X.Opens))
    (hf : f ∈ nonZeroDivisors (Γ(X, U)))
    (hgen : D.ideal U = Ideal.span ({f} : Set (Γ(X, U)))) :
    (weilDivisor_ofEffectiveCartier D).coeff Z =
      ((Ring.ord (X.presheaf.stalk Z.genericPoint)
          (X.presheaf.germ (U : X.Opens) Z.genericPoint hξ f)).toNat : ℤ) := sorry

end AlgebraicGeometry.Scheme
