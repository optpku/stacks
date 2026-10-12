/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.RingTheory.Depth

/-!
# Slicing by a fibre-regular equation

This file constructs relative effective Cartier divisors by extending a germ that is regular
on a fibre.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A germ in the maximal ideal whose restriction to the fibre is a nonzerodivisor extends on
an affine neighbourhood to an equation for a relative effective Cartier divisor through the
point, locally of finite presentation over the base. -/
@[stacks 056Y]
theorem exists_affineOpen_relativeEffectiveCartierDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (x : X) (h : X.presheaf.stalk x)
    (hmax : h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hflat : f.flatAt x)
    (hreg : (sourceStalkToFiberStalk f x).hom h ∈
      nonZeroDivisors (fiberStalkAt f x)) :
    ∃ U : X.affineOpens,
      ∃ hxU : x ∈ (U : X.Opens),
        ∃ hU : Γ(X, (U : X.Opens)),
          X.presheaf.germ (U : X.Opens) x hxU hU = h ∧
            let D : (U : X.Opens).toScheme.IdealSheafData :=
              Scheme.IdealSheafData.ofIdealTop
                (Ideal.span ({(U : X.Opens).topIso.inv hU} : Set (Γ((U : X.Opens), ⊤))))
            (⟨x, hxU⟩ ∈ D.support ∧
              IsRelativeEffectiveCartierDivisor ((U : X.Opens).ι ≫ f) D ∧
                LocallyOfFinitePresentation
                  (D.subschemeι ≫ ((U : X.Opens).ι ≫ f))) := sorry

/-- A locally finitely presented morphism that is flat at a point admits, when the fibre stalk
has depth at least one, a relative effective Cartier divisor through that point on an affine
neighbourhood whose morphism to the base is of finite presentation. -/
@[stacks 056Z]
theorem exists_relativeEffectiveCartierDivisor_of_one_le_depth
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (x : X) (hflat : f.flatAt x)
    (hdepth : (1 : ℕ∞) ≤ moduleDepth (fiberStalkAt f x) (fiberStalkAt f x)) :
    ∃ U : X.affineOpens,
      ∃ hxU : x ∈ (U : X.Opens),
        ∃ D : (U : X.Opens).toScheme.IdealSheafData,
          ⟨x, hxU⟩ ∈ D.support ∧
            IsRelativeEffectiveCartierDivisor ((U : X.Opens).ι ≫ f) D ∧
              Scheme.Hom.FinitePresentation
                (D.subschemeι ≫ ((U : X.Opens).ι ≫ f)) := sorry

end AlgebraicGeometry.Scheme.Hom
