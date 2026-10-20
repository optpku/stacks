/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Prime
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension
public import ReasLib.Topology.Specialization.Dimension.Catenary
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Affine

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- At a generic point of a locally principal closed subscheme of a locally Noetherian scheme,
the ambient local ring has Krull dimension at most one. -/
theorem ringKrullDim_stalk_le_one_of_mem_genericPoints
    (D : X.IdealSheafData) [IsLocallyPrincipalClosedSubscheme D.subschemeι] {ξ : D.subscheme}
    (hξ : ξ ∈ genericPoints D.subscheme) :
    ringKrullDim (X.presheaf.stalk (D.subschemeι.base ξ)) ≤ 1 := sorry

end AlgebraicGeometry.IsLocallyPrincipalClosedSubscheme

namespace AlgebraicGeometry.IsEffectiveCartierDivisor

/-- The local ring of an effective Cartier divisor has strictly smaller Krull dimension than
the ambient local ring whenever the latter has finite Krull dimension. -/
theorem ringKrullDim_subscheme_stalk_lt {X : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (x : D.subscheme)
    (hfin : ringKrullDim (X.presheaf.stalk (D.subschemeι.base x)) < ⊤) :
    ringKrullDim (D.subscheme.presheaf.stalk x) <
      ringKrullDim (X.presheaf.stalk (D.subschemeι.base x)) := sorry

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- At a generic point of an effective Cartier divisor on a locally Noetherian scheme,
the ambient local ring has Krull dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_mem_genericPoints
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] {ξ : D.subscheme}
    (hξ : ξ ∈ genericPoints D.subscheme) :
    ringKrullDim (X.presheaf.stalk (D.subschemeι.base ξ)) = 1 := sorry

end AlgebraicGeometry.IsEffectiveCartierDivisor

namespace AlgebraicGeometry.Scheme.Hom

/-- For an integral closed subscheme of an integral scheme locally of finite type over a
universally catenary dimensioned base, coheight one is equivalent to a one-step drop in
`δ`-dimension. -/
theorem coheight_eq_one_iff_deltaDimension_eq_sub_one
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X]
    (Z : X.IdealSheafData) [IsIntegral Z.subscheme] :
    Order.coheight
        (toIrreducibleCloseds (Z.subschemeι (genericPoint Z.subscheme))) = 1 ↔
      p.deltaDimension δ
          (toIrreducibleCloseds (Z.subschemeι (genericPoint Z.subscheme))) =
        p.deltaDimension δ (toIrreducibleCloseds (genericPoint X)) - 1 := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.PrimeDivisor

/-- The support of a prime divisor has `δ`-dimension one less than its integral ambient
scheme. -/
theorem deltaDimension_eq_sub_one
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X] (Z : PrimeDivisor X) :
    p.deltaDimension δ Z.support =
      p.deltaDimension δ
        (toIrreducibleCloseds (_root_.genericPoint X)) - 1 := sorry

end AlgebraicGeometry.PrimeDivisor

namespace AlgebraicGeometry.Scheme.Hom

/-- Every irreducible component of an effective Cartier divisor on an integral scheme has
`δ`-dimension one less than the ambient scheme. -/
theorem effectiveCartierComponent_deltaDimension_eq_sub_one
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] [IsIntegral X]
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (C : irreducibleComponents D.subscheme) :
    p.deltaDimension δ
        (toIrreducibleCloseds (D.subschemeι (genericPoints.ofComponent C).1)) =
      p.deltaDimension δ (toIrreducibleCloseds (genericPoint X)) - 1 := sorry

end AlgebraicGeometry.Scheme.Hom
