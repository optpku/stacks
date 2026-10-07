module

public import stacks_project.Chap111.Definition_111_49_1_Weil
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Stalk
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.LocallyRingedSpace
open CategoryTheory Opposite TopCat.Presheaf

universe u

/- Definition 111.49.1 (1): a Weil divisor on a Noetherian integral scheme `X` is a formal
integer linear combination of prime divisors. This is the owner `WeilDivisor`. -/
@[stacks 02AR]
#check @WeilDivisor

/- Definition 111.49.1 (2): a prime divisor on `X` is an integral closed subscheme `Z ⊆ X`
whose generic point `ξ` has `ringKrullDim (𝒪_{X, ξ}) = 1`. This is the owner `PrimeDivisor`. -/
@[stacks 02AR]
#check @PrimeDivisor

#check @PrimeDivisor.ringKrullDim_genericPointStalk
#check @Scheme.mem_stalkInFunctionField_iff

/- Definition 111.49.1 (3): the Weil divisor associated to a rational function `f ∈ K(X)ˣ`
is `∑ v_Z(f) [Z]`, where `v_Z` is the order of vanishing along the prime divisor `Z`.
This is the owner `principalWeilDivisor`. -/
@[stacks 02AR]
#check @principalWeilDivisor

/-- A unit in the local ring of a prime divisor has vanishing principal coefficient. -/
theorem principalWeilDivisor_coeff_eq_zero_of_isUnit_stalk {X : Scheme.{u}}
    [IsNoetherian X] [IsIntegral X] (f : X.functionFieldˣ) (Z : PrimeDivisor X)
    (a : X.presheaf.stalk Z.genericPoint) (ha : IsUnit a)
    (hfa : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a = f) :
    (principalWeilDivisor X f).coeff Z = 0 :=
  sorry

/-- If a rational function lies in the local ring of a prime divisor, its coefficient is the
length of that local ring modulo the corresponding principal ideal. -/
theorem principalWeilDivisor_coeff_eq_length {X : Scheme.{u}}
    [IsNoetherian X] [IsIntegral X] (f : X.functionFieldˣ) (Z : PrimeDivisor X)
    (a : X.presheaf.stalk Z.genericPoint)
    (hfa : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a = f) :
    (principalWeilDivisor X f).coeff Z =
      ((Ring.ord (X.presheaf.stalk Z.genericPoint) a).toNat : ℤ) :=
  sorry

/-- If a rational function is a ratio `a / b` in the local ring of a prime divisor, its
coefficient is the difference of the corresponding lengths. -/
theorem principalWeilDivisor_coeff_eq_length_sub {X : Scheme.{u}}
    [IsNoetherian X] [IsIntegral X] (f : X.functionFieldˣ) (Z : PrimeDivisor X)
    (a b : X.presheaf.stalk Z.genericPoint)
    (hb : algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField b ≠ 0)
    (hfa :
      algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField a /
          algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField b =
        f) :
    (principalWeilDivisor X f).coeff Z =
      ((Ring.ord (X.presheaf.stalk Z.genericPoint) a).toNat : ℤ) -
        ((Ring.ord (X.presheaf.stalk Z.genericPoint) b).toNat : ℤ) :=
  sorry

/- Definition 111.49.1 (4): an effective Cartier divisor on a scheme `S` is a closed subscheme
which is locally cut out by a nonzerodivisor on affine opens. The mathlib-style owner is
`IsEffectiveCartierDivisor`; the affine-local generator form is
`AffineLocalNonZeroDivisorGenerator`. -/
@[stacks 02AR]
#check @IsEffectiveCartierDivisor

#check @AffineLocalNonZeroDivisorGenerator
#check @isEffectiveCartierDivisor_iff_affineLocalNonZeroDivisorGenerator

/- Definition 111.49.1 (5): the Weil divisor associated to an effective Cartier divisor `D ⊆ X`
is `∑ v_Z(D) [Z]`, with `v_Z(D)` the length-order of a local nonzerodivisor equation along each
prime divisor. -/
@[stacks 02AR]
#check @weilDivisor_ofEffectiveCartier

/- Definition 111.49.1 (6): the sheaf of total quotient rings `𝒦_S` is the sheafification of the
presheaf sending `U` to the localization of `𝒪_S(U)` at sections whose germs are nonzerodivisors.
This is the owner `meromorphicFunctionSheaf`. -/
@[stacks 02AR]
#check @meromorphicFunctionSheaf

#check @meromorphicFunctionDenominators
#check @TopCat.Presheaf.totalQuotientPresheaf
#check @toMeromorphicFunctionSheafHom

/- Definition 111.49.1 (7): a Cartier divisor on a scheme `S` is a global section of the quotient
sheaf `𝒦_S^⁎ / 𝒪_S^⁎`. This is the owner `CartierDivisor`. -/
@[stacks 02AR]
#check @CartierDivisor

#check @cartierDivisorAddSheaf
#check @cartierDivisorShortComplex
#check @cartierDivisorShortComplex_shortExact

/- Definition 111.49.1 (8): the Weil divisor associated to a Cartier divisor
`τ ∈ Γ(X, 𝒦_X^⁎ / 𝒪_X^⁎)` is `∑ v_Z(τ) [Z]`, with `v_Z(τ)` the length-order of a local
meromorphic representative `a / b` along each prime divisor. -/
@[stacks 02AR]
#check @weilDivisor_ofCartier

#check @cartierOrder
#check @weilDivisor_ofCartier_coeff
