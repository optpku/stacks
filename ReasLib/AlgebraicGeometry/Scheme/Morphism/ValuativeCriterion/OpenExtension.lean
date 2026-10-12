/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.Scheme.GermInjective

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace ValuativeCriterion.Existence

/-- A morphism defined on an open subscheme extends across a closure point when the target
morphism satisfies the existence part of the valuative criterion and the source is
germ-injective there. -/
theorem exists_openExtensionAtPoint
    {S X Y : Scheme.{u}} {fX : X ⟶ S} {fY : Y ⟶ S} {x : X} {U : X.Opens}
    (h_valuative : ValuativeCriterion.Existence fY)
    [LocallyOfFiniteType fY] [IsSeparated fY]
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)]
    [X.IsGermInjectiveAt x]
    (f : U.toScheme ⟶ Y) (hf_over : f ≫ fY = U.ι ≫ fX)
    (hx_closure : x ∈ closure (U : Set X)) :
    ∃ (U' : X.Opens) (hUU' : U ≤ U') (_ : x ∈ U') (f' : U'.toScheme ⟶ Y),
      f' ≫ fY = U'.ι ≫ fX ∧ X.homOfLE hUU' ≫ f' = f := sorry

end ValuativeCriterion.Existence

/-- A morphism from an open subscheme to a proper target extends across a closure point when
the source is reduced with finitely many irreducible components or is Noetherian and the stalk
at that point is a valuation ring. -/
theorem exists_openExtensionAtPoint_of_isProper_of_stalk_valuationRing
    {S X Y : Scheme.{u}} {fX : X ⟶ S} {fY : Y ⟶ S} {x : X} {U : X.Opens}
    (f : U.toScheme ⟶ Y) (hf_over : f ≫ fY = U.ι ≫ fX)
    (hx_closure : x ∈ closure (U : Set X))
    [IsProper fY]
    [IsDomain (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk x)]
    (hX : (IsReduced X ∧ Finite (irreducibleComponents X)) ∨ IsNoetherian X) :
    ∃ (U' : X.Opens) (hUU' : U ≤ U') (_ : x ∈ U') (f' : U'.toScheme ⟶ Y),
      f' ≫ fY = U'.ι ≫ fX ∧ X.homOfLE hUU' ≫ f' = f := sorry

end AlgebraicGeometry
