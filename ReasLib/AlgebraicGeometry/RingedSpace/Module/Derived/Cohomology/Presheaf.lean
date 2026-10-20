/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.UnderlyingSheaf
public import ReasLib.Algebra.Category.Grp.Presheaf.Derived
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology presheaves and sheaves on a ringed space

The cohomology presheaf is obtained by deriving the underlying additive presheaf functor.
Its sheafification is naturally the underlying additive cohomology sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

attribute [instance] AlgebraicGeometry.RingedSpace.moduleUnderlyingPresheaf_additive
  AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_additive
  AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_preservesFiniteLimits
  AlgebraicGeometry.RingedSpace.moduleUnderlyingSheaf_preservesFiniteColimits

namespace TopCat

/-- Additive presheaves on a topological space carry the standard derived-category model. -/
instance additivePresheafHasDerivedCategory (X : TopCat.{u}) :
    HasDerivedCategory (X.Presheaf AddCommGrpCat.{u}) :=
  inferInstanceAs (HasDerivedCategory ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}))

/-- Additive sheaves on a topological space have their canonical abelian homology structure. -/
instance additiveSheafCategoryWithHomology (X : TopCat.{u}) :
    CategoryWithHomology (X.Sheaf AddCommGrpCat.{u}) :=
  CategoryTheory.categoryWithHomology_of_abelian

end TopCat

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Cohomology

/-- The functor assigning the degree-`m` cohomology presheaf to a derived module. -/
abbrev cohomologyPresheafFunctor (X : RingedSpace.{u}) (m : ℤ) :
    ModuleDerived X ⥤ (Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  Functor.RightDerived.Cochain.functor (moduleUnderlyingPresheaf X) ⋙
    DerivedCategory.homologyFunctor _ m

end AlgebraicGeometry.RingedSpace.ModuleDerived.Limit.Cohomology

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

variable {X : RingedSpace.{u}}

/-- The degree-`q` additive cohomology presheaf of a derived `𝒪_X`-module. -/
@[stacks 0BKJ "objectwise cohomology presheaf on a ringed space"]
abbrev presheaf (X : RingedSpace.{u}) (K : ModuleDerived X) (q : ℤ) :
    (Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Limit.Cohomology.cohomologyPresheafFunctor X q).obj K

/-- The degree-`q` additive cohomology sheaf of a derived `𝒪_X`-module. -/
@[stacks 0BKJ "cohomology sheaf on a ringed space"]
abbrev sheaf (X : RingedSpace.{u}) (K : ModuleDerived X) (q : ℤ) :
    X.carrier.Sheaf AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf X).obj ((DerivedCategory.homologyFunctor X.Modules q).obj K)

/-- The module-valued iterated open cohomology object `H^p(U, H^q(K))`. -/
@[stacks 0BKJ "iterated open cohomology object"]
abbrev openCohomology (E : ModuleDerived X) (U : Opens X.carrier) (p : ℕ) (q : ℤ) :
    ModuleCat (sectionsRingOnOpen X U) :=
  moduleCohomologyAtOpen U ((DerivedCategory.homologyFunctor X.Modules q).obj E) p

set_option backward.privateInPublic true in
/-- Sheafification makes the derived comparison unit an isomorphism on cohomology. -/
@[instance]
private theorem sheafifiedDerivedUnit_isIso (X : RingedSpace.{u})
    (C : CochainComplex X.Modules ℤ) (q : ℤ) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).map
      ((DerivedCategory.homologyFunctor (X.carrier.Presheaf AddCommGrpCat.{u}) q).map
        ((Functor.RightDerived.Cochain.unit (moduleUnderlyingPresheaf X)).app C))) := sorry

set_option backward.privateInPublic true in
/-- Sheafifying the underlying presheaf of a module recovers its underlying sheaf. -/
private def underlyingSheafificationIso (X : RingedSpace.{u}) :
    moduleUnderlyingPresheaf X ⋙
        presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ≅
      moduleUnderlyingSheaf X :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleUnderlyingSheaf X)
      (CategoryTheory.sheafificationNatIso
        (J := Opens.grothendieckTopology X.carrier) (D := AddCommGrpCat.{u})).symm ≪≫
    Functor.rightUnitor _

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical identification of sheafified cohomology with the additive cohomology sheaf. -/
def sheafificationIso (X : RingedSpace.{u}) (K : ModuleDerived X) (q : ℤ) :
    (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (presheaf X K q) ≅ sheaf X K q := by
  let representative :=
    (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X).objPreimage K
  let representativeIso :=
    (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X).objObjPreimageIso K
  let underlyingComplex := ((moduleUnderlyingPresheaf X).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj representative
  have sheafificationAdditive :
      (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).Additive :=
    CategoryTheory.presheafToSheaf_additive
  have sheafificationFiniteLimits : PreservesFiniteLimits
      (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    inferInstance
  have sheafificationFiniteColimits : PreservesFiniteColimits
      (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    inferInstance
  exact (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).mapIso
      ((Limit.Cohomology.cohomologyPresheafFunctor X q).mapIso representativeIso.symm) ≪≫
    (asIso ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).map
      ((DerivedCategory.homologyFunctor (X.carrier.Presheaf AddCommGrpCat.{u}) q).map
        ((Functor.RightDerived.Cochain.unit (moduleUnderlyingPresheaf X)).app representative)))).symm ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).mapIso
      ((DerivedCategory.homologyFunctorFactors (X.carrier.Presheaf AddCommGrpCat.{u}) q).app underlyingComplex) ≪≫
    (underlyingComplex.mapHomologyIso
      (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :
        X.carrier.Presheaf AddCommGrpCat.{u} ⥤ X.carrier.Sheaf AddCommGrpCat.{u}) q).symm ≪≫
    (HomologicalComplex.homologyFunctor (X.carrier.Sheaf AddCommGrpCat.{u}) (ComplexShape.up ℤ) q).mapIso
      (((Functor.mapHomologicalComplexCompIso (Iso.refl (moduleUnderlyingPresheaf X ⋙
        (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :
          X.carrier.Presheaf AddCommGrpCat.{u} ⥤ X.carrier.Sheaf AddCommGrpCat.{u})))
        (ComplexShape.up ℤ)).app representative) ≪≫
        ((NatIso.mapHomologicalComplex (underlyingSheafificationIso X)
          (ComplexShape.up ℤ)).app representative)) ≪≫
    representative.mapHomologyIso (moduleUnderlyingSheaf X) q ≪≫
    (moduleUnderlyingSheaf X).mapIso
      ((DerivedCategory.homologyFunctorFactors X.Modules q).app representative).symm ≪≫
    (DerivedCategory.homologyFunctor X.Modules q ⋙ moduleUnderlyingSheaf X).mapIso representativeIso

/-- The canonical sheafification identification is natural in the derived module. -/
theorem sheafificationIso_hom_naturality (X : RingedSpace.{u})
    {K L : ModuleDerived X} (f : K ⟶ L) (q : ℤ) :
    (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).map
        ((Limit.Cohomology.cohomologyPresheafFunctor X q).map f) ≫
      (sheafificationIso X L q).hom =
    (sheafificationIso X K q).hom ≫
      (DerivedCategory.homologyFunctor X.Modules q ⋙ moduleUnderlyingSheaf X).map f := sorry

/-- Sheafification of the cohomology-presheaf functor is the cohomology-sheaf functor. -/
def sheafificationNatIso (X : RingedSpace.{u}) (q : ℤ) :
    Limit.Cohomology.cohomologyPresheafFunctor X q ⋙
        presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ≅
      DerivedCategory.homologyFunctor X.Modules q ⋙ moduleUnderlyingSheaf X :=
  NatIso.ofComponents (fun K => sheafificationIso X K q)
    (fun f => sheafificationIso_hom_naturality X f q)

/-- The sheaf associated to the degree-`q` cohomology presheaf is the degree-`q` cohomology sheaf. -/
@[stacks 0BKJ "sheafification of the objectwise cohomology presheaf"]
theorem sheafification_isomorphic (X : RingedSpace.{u}) (K : ModuleDerived X) (q : ℤ) :
    IsIsomorphic (sheaf X K q)
      ((presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}).obj
        (presheaf X K q)) := sorry

/-- Evaluation of the cohomology presheaf over an open is canonically the corresponding open
hypercohomology group. -/
@[stacks 0BKJ "cohomology presheaf evaluated on an open"]
theorem presheaf_obj_isomorphic_openHypercohomology
    (X : RingedSpace.{u}) (K : ModuleDerived X) (q : ℤ) (U : Opens X.carrier) :
    IsIsomorphic ((presheaf X K q).obj (op U))
      (moduleOpenHypercohomology X U K q) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

namespace AlgebraicGeometry.RingedSpaceCohomology

/-- `𝓗'[q](X, K)` is the canonical degree-`q` additive cohomology presheaf. -/
scoped notation:max "𝓗'[" q "](" X ", " K ")" =>
  AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.presheaf X K q

/-- `𝓗[q](X, K)` is the degree-`q` additive cohomology sheaf. -/
scoped notation:max "𝓗[" q "](" X ", " K ")" =>
  AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology.sheaf X K q

end AlgebraicGeometry.RingedSpaceCohomology

end
