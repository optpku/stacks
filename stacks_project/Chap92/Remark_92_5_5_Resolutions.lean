module

public import ReasLib.Algebra.PolynomialSite.Resolution
public import ReasLib.RingTheory.CotangentComplex.Resolution
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.PolynomialEvaluation
import StacksCheckRecall

/-!
# Polynomial simplicial resolutions of an algebra

Remark 92.5.5 defines polynomial simplicial resolutions, records their equivalent
characterizations and existence, and computes derived lower shriek and cotangent complexes
using any such resolution.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Algebra
open Algebra.PolynomialSite
open CommAlgCat.Over.Polynomial.Site
open SSet.modelCategoryQuillen
open AlgebraicTopology
open HomologicalComplex
open scoped CategoryTheory

universe u q q'

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {P : SimplicialObject (CommAlgCat.{u} A)}
variable (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))

/- Remark 92.5.5 (Resolutions) (1): a resolution of `B` over `A` is an augmented
simplicial `A`-algebra `ε : P ⟶ B` with each `P.obj n` a polynomial `A`-algebra and
with `ε` a trivial Kan fibration of simplicial sets. -/
@[stacks 08QI]
#check (Algebra.PolynomialSite.IsResolution ε : Prop)

section Characterization

variable (hP : ∀ n, IsPolynomial A (P.obj n))
variable (h_surj : ∀ n, Function.Surjective ((forget (CommAlgCat.{u} A)).map (ε.app n)))

/- Remark 92.5.5 (Resolutions) (2): if each `P.obj n` is a polynomial `A`-algebra
surjecting onto `B`, then being a resolution, a quasi-isomorphism on associated complexes,
and a homotopy equivalence of simplicial sets are equivalent. -/
@[stacks 08QI]
#check (Algebra.PolynomialSite.isResolution_tfae ε hP h_surj :
  List.TFAE
    [IsResolution ε,
      QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (underlyingAddCommGrpMap ε)),
      IsHomotopyEquivalence (underlyingSSetMap ε)])

#check (Algebra.PolynomialSite.isResolution_iff_quasiIso ε hP h_surj :
  IsResolution ε ↔
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (underlyingAddCommGrpMap ε)))

#check (Algebra.PolynomialSite.isResolution_iff_homotopyEquivalence ε hP h_surj :
  IsResolution ε ↔ IsHomotopyEquivalence (underlyingSSetMap ε))

end Characterization

section Evaluation

variable (hP : ∀ n, IsPolynomial A (P.obj n))
variable (hε : I.rlp (underlyingSSetMap ε))

section AbelianGroups

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q'} AddCommGrpCat.{u}]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) AddCommGrpCat.{u})
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (ComplexShape.up ℤ))]

/- Remark 92.5.5 (Resolutions) (3): a resolution gives a cosimplicial polynomial-site
object, and derived lower shriek is computed functorially by evaluation on it. -/
@[stacks 08QI]
#check (Algebra.PolynomialSite.lowerShriek_eval_abelian ε hP hε :
  IsIsomorphic
    ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u}) (0 : ℤ)) ⋙
      Lπ![(PolynomialSite A B), AddCommGrpCat.{u}])
    (CosimplicialObject.Evaluation.toDerived AddCommGrpCat.{u} (asCosimplicial ε hP)))

end AbelianGroups

section Modules

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

#check (Algebra.PolynomialSite.lowerShriek_eval_module ε hP hε :
  IsIsomorphic
    ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B) (0 : ℤ)) ⋙
      Lπ![(PolynomialSite A B), (ModuleCat.{u} B)])
    (CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B) (asCosimplicial ε hP)))

end Modules

end Evaluation

/- Remark 92.5.5 (Resolutions) (4): resolutions exist for every ring map `A → B`.
The formal construction does not require the simplicial computations for the standard
resolution. -/
@[stacks 08QI]
#check (Algebra.PolynomialSite.exists_resolution A B :
  ∃ (P : SimplicialObject (CommAlgCat.{u} A))
    (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)),
    IsResolution ε)

/- Remark 92.5.5 (Resolutions) (5): the standard resolution of `B` over `A` is a
resolution, so the terminology agrees with that construction. -/
@[stacks 08QI]
#check (Algebra.PolynomialSite.instIsResolution_standardHom A B :
  IsResolution (standardHom A B))

section CotangentComplex

variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]
variable [IsResolution ε]

/- Remark 92.5.5 (Resolutions) (6): any resolution computes the cotangent complex in
`D(B)` by evaluation of the presheaf of scalar-extended differentials. -/
@[stacks 08QI]
#check (Algebra.CotangentComplex.cotangentComplex_iso_eval ε :
  IsIsomorphic
    (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
    ((CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B)
        (IsResolution.asCosimplicial ε)).obj (omegaSheaf A B)))

end CotangentComplex
