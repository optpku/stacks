module

public import ReasLib.RingTheory.CotangentComplex.Basic
public import ReasLib.Algebra.PolynomialSite.Differentials
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.StandardPolynomialEvaluation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complexes and the polynomial site

The cotangent complex is computed by derived lower shriek of the presheaf of
scalar-extended Kähler differentials on the opposite polynomial site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open Algebra.PolynomialSite
open CommAlgCat.Over.Polynomial.Site
open scoped CategoryTheory

universe u q q'

namespace Algebra.CotangentComplex

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/-- The cotangent complex of an algebra is canonically isomorphic in its derived category
to derived lower shriek of the presheaf of scalar-extended Kähler differentials, placed
in degree zero, on the opposite polynomial site. -/
@[stacks 08PU]
theorem lowerShriek_omega :
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
        ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
            (0 : ℤ)).obj (omegaSheaf A B))) :=
  sorry

end Algebra.CotangentComplex
