module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.LocallyPrincipal
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber criteria for relative effective Cartier divisors

This file owns the local construction of a relative effective Cartier divisor from a Cartier
divisor in one fiber, together with the resulting global fiber criteria.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace IsRelativeEffectiveCartierDivisor

/-- A Cartier divisor in one fiber extends locally to a relative effective Cartier divisor
containing the given closed subscheme and having the same fiber. -/
@[stacks 062Y]
theorem exists_open_le_fiber_eq_of_isEffectiveCartierDivisor_near
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData) (x : Z.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (Z.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (Z.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (Z.subschemeι x)))) ∧
          IsEffectiveCartierDivisor
            ((Z.comap (Scheme.Hom.fiberι f (f (Z.subschemeι x)))).comap W.ι).subschemeι) :
    ∃ U : X.Opens,
      ∃ _ : Z.subschemeι x ∈ (U : Set X),
        ∃ D : U.toScheme.IdealSheafData,
          ∃ _ : IsRelativeEffectiveCartierDivisor (U.ι ≫ f) D,
            ∃ _ : D ≤ Z.comap U.ι,
              (Z.comap U.ι).comap
                  (Scheme.Hom.fiberι (U.ι ≫ f) (f (Z.subschemeι x))) =
                D.comap (Scheme.Hom.fiberι (U.ι ≫ f) (f (Z.subschemeι x))) := sorry

/-- Finite presentation and flatness of a closed subscheme at a point allow a local relative
effective Cartier extension to equal the closed subscheme. -/
@[stacks 062Y]
theorem exists_open_eq_of_finitePresentation_flatAt
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData) (x : Z.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    [Scheme.Hom.FinitePresentation Z.subschemeι]
    (hZflat : Scheme.Hom.flatAt (Z.subschemeι ≫ f) x)
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (Z.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (Z.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (Z.subschemeι x)))) ∧
          IsEffectiveCartierDivisor
            ((Z.comap (Scheme.Hom.fiberι f (f (Z.subschemeι x)))).comap W.ι).subschemeι) :
    ∃ U : X.Opens,
      ∃ _ : Z.subschemeι x ∈ (U : Set X),
        ∃ D : U.toScheme.IdealSheafData,
          ∃ _ : IsRelativeEffectiveCartierDivisor (U.ι ≫ f) D,
            Z.comap U.ι = D := sorry

/-- Local principality near a point allows a local relative effective Cartier extension to equal
the closed subscheme. -/
@[stacks 062Y]
theorem exists_open_eq_of_locallyPrincipal_near
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData) (x : Z.subscheme)
    [Flat f] [LocallyOfFinitePresentation f]
    (hprincipal :
      ∃ V : X.Opens,
        ∃ _ : Z.subschemeι x ∈ (V : Set X),
          IsLocallyPrincipalClosedSubscheme (Z.comap V.ι).subschemeι)
    (hfiber :
      ∃ W : (Scheme.Hom.fiber f (f (Z.subschemeι x))).Opens,
        Scheme.Hom.asFiber f (Z.subschemeι x) ∈
            (W : Set (Scheme.Hom.fiber f (f (Z.subschemeι x)))) ∧
          IsEffectiveCartierDivisor
            ((Z.comap (Scheme.Hom.fiberι f (f (Z.subschemeι x)))).comap W.ι).subschemeι) :
    ∃ U : X.Opens,
      ∃ _ : Z.subschemeι x ∈ (U : Set X),
        ∃ D : U.toScheme.IdealSheafData,
          ∃ _ : IsRelativeEffectiveCartierDivisor (U.ι ≫ f) D,
            Z.comap U.ι = D := sorry

/-- A flat locally finitely presented closed subscheme whose fibers are effective Cartier
divisors is a relative effective Cartier divisor. -/
@[stacks 062Y]
theorem of_flat_locallyOfFinitePresentation_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData)
    [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation (Z.subschemeι ≫ f)] [Flat (Z.subschemeι ≫ f)]
    (hfibers : ∀ s : S,
      IsEffectiveCartierDivisor (Z.comap (Scheme.Hom.fiberι f s)).subschemeι) :
    IsRelativeEffectiveCartierDivisor f Z := sorry

/-- A locally principal closed subscheme whose fibers are effective Cartier divisors is a
relative effective Cartier divisor. -/
@[stacks 062Y]
theorem of_locallyPrincipal_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : X.IdealSheafData)
    [Flat f] [LocallyOfFinitePresentation f]
    [IsLocallyPrincipalClosedSubscheme Z.subschemeι]
    (hfibers : ∀ s : S,
      IsEffectiveCartierDivisor (Z.comap (Scheme.Hom.fiberι f s)).subschemeι) :
    IsRelativeEffectiveCartierDivisor f Z := sorry

end IsRelativeEffectiveCartierDivisor
end AlgebraicGeometry
