module

public import ReasLib.Algebra.PolynomialSite.Resolution
public import ReasLib.RingTheory.CotangentComplex.PolynomialSite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.PolynomialEvaluation

/-!
# Computing cotangent complexes with polynomial simplicial resolutions

Any polynomial simplicial resolution computes the cotangent complex by evaluation of the
presheaf of scalar-extended Kähler differentials.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Algebra.PolynomialSite
open CommAlgCat.Over.Polynomial.Site
open scoped CategoryTheory

universe u q q'

namespace Algebra.CotangentComplex

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {P : SimplicialObject (CommAlgCat.{u} A)}
variable (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))

/-- The cotangent complex of an algebra is isomorphic in its derived category to evaluation
of the presheaf of scalar-extended Kähler differentials on any polynomial simplicial
resolution. -/
@[stacks 08QI]
theorem cotangentComplex_iso_eval
    [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
    [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
    [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
      (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
        (ComplexShape.up ℤ))]
    [IsResolution ε] :
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B)
          (IsResolution.asCosimplicial ε)).obj (omegaSheaf A B)) :=
  sorry

end Algebra.CotangentComplex
