/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.Algebra.Category.Grp.Presheaf.Derived
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of Derived Modules on Ringed Sites

The underlying presheaf of a module sheaf is only left exact, so its action on an arbitrary
derived module is modeled by a total right derived functor.  This file owns that functor and the
resulting cohomology presheaves, separately from the ordinary cohomology sheaves in the module
category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): generic derived-presheaf and homology APIs must align with the canonical RingedSite.Hom.ModuleDerived presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable (X : RingedSite.{u, v, w})

/-- Forget a module sheaf on `X` to its underlying sheaf of additive groups. -/
@[stacks 0BKV "underlying additive sheaf of a ringed-site module"]
abbrev underlyingSheafFunctor
    (X : RingedSite.{u, v, w}) :
    ModuleCat.{z} X ⥤ Sheaf X.siteTopology AddCommGrpCat.{z} :=
  SheafOfModules.toSheaf X.structureSheaf

/-- Forget a module sheaf on `X` to its underlying additive presheaf. -/
@[stacks 0BKV "underlying additive presheaf of a ringed-site module"]
abbrev underlyingPresheafFunctor
    (X : RingedSite.{u, v, w}) :
    ModuleCat.{z} X ⥤ (Xᵒᵖ ⥤ AddCommGrpCat.{z}) :=
  underlyingSheafFunctor X ⋙
    sheafToPresheaf X.siteTopology AddCommGrpCat.{z}

/-- The underlying-additive-presheaf functor is additive. -/
@[stacks 0BKV "additivity of the underlying additive presheaf functor"]
theorem underlyingPresheafFunctor_additive :
    (underlyingPresheafFunctor X).Additive := inferInstance

/-- A Grothendieck-abelian module category supplies the total right-derived
underlying-presheaf functor. -/
@[stacks 0BKV "existence of the derived underlying additive presheaf"]
theorem underlyingPresheafFunctor_hasRightDerived
    [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
    (@Functor.RightDerived.Cochain.toDerived
      (ModuleCat.{z} X) (Xᵒᵖ ⥤ AddCommGrpCat.{z})
      inferInstance inferInstance inferInstance inferInstance inferInstance
      (underlyingPresheafFunctor X) (underlyingPresheafFunctor_additive X)).HasRightDerivedFunctor
        (HomologicalComplex.quasiIso (ModuleCat.{z} X) (ComplexShape.up ℤ)) := sorry

/-- The total right derived underlying-presheaf functor on derived modules over `X`. -/
@[stacks 0BKV "derived underlying additive presheaf"]
noncomputable abbrev underlyingPresheafDerived
    [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
  RingedSite.Hom.ModuleDerived.{z} X ⥤
      DerivedCategory (Xᵒᵖ ⥤ AddCommGrpCat.{z}) :=
  @Functor.RightDerived.Cochain.functor
    (ModuleCat.{z} X) (Xᵒᵖ ⥤ AddCommGrpCat.{z})
    inferInstance inferInstance (RingedSite.Hom.moduleCat_hasDerivedCategory X)
    inferInstance inferInstance inferInstance
    (underlyingPresheafFunctor X) (underlyingPresheafFunctor_additive X)
    (underlyingPresheafFunctor_hasRightDerived X)

/-- The additive presheaf `U ↦ H^q(U, K)` associated to a derived module `K` on `X`. -/
@[stacks 0BKV "objectwise cohomology presheaf of a derived module"]
abbrev cohomologyPresheaf [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    (K : RingedSite.Hom.ModuleDerived.{z} X) (q : ℤ) :
    Xᵒᵖ ⥤ AddCommGrpCat.{z} :=
  (DerivedCategory.homologyFunctor (Xᵒᵖ ⥤ AddCommGrpCat.{z}) q).obj
    ((underlyingPresheafDerived X).obj K)

/-- The degree-`q` cohomology module sheaf of a derived module `K` on `X`. -/
@[stacks 0BKV "cohomology sheaf of a derived module"]
abbrev cohomologySheaf
    [UnivLE.{max u v, z}]
    (K : RingedSite.Hom.ModuleDerived.{z} X) (q : ℤ) : ModuleCat.{z} X :=
  (@DerivedCategory.homologyFunctor
    (ModuleCat.{z} X) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory X) q).obj K

/-- The morphism on degree-`q` cohomology module sheaves induced by `f : K ⟶ L`. -/
@[stacks 0BKV "morphism on cohomology sheaves"]
abbrev cohomologySheafMap (q : ℤ)
    [UnivLE.{max u v, z}]
    {K L : RingedSite.Hom.ModuleDerived.{z} X} (f : K ⟶ L) :
    cohomologySheaf X K q ⟶ cohomologySheaf X L q :=
  (@DerivedCategory.homologyFunctor
    (ModuleCat.{z} X) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory X) q).map f

/-- The underlying additive sheaf of the degree-`q` cohomology module sheaf of `K`. -/
@[stacks 0BKV "underlying additive cohomology sheaf"]
abbrev underlyingCohomologySheaf
    [UnivLE.{max u v, z}]
    (K : RingedSite.Hom.ModuleDerived.{z} X) (q : ℤ) :
    Sheaf X.siteTopology AddCommGrpCat.{z} :=
  (underlyingSheafFunctor X).obj (cohomologySheaf X K q)

/-- The degree-`q` cohomology group of a derived module `K` over an object `U` of `X`. -/
@[stacks 0BKV "cohomology over an object of a ringed site"]
abbrev cohomologyOverObject [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    (U : X) (K : RingedSite.Hom.ModuleDerived.{z} X) (q : ℤ) : AddCommGrpCat.{z} :=
  (cohomologyPresheaf X K q).obj (op U)

/-- Sheafifying `U ↦ H^q(U, K)` gives the underlying additive sheaf of the cohomology
module sheaf of `K`. -/
@[stacks 0BKV]
theorem sheafification_cohomologyPresheaf_isomorphic_underlyingCohomologySheaf
    [UnivLE.{max u v, z}]
    [HasSheafify X.siteTopology AddCommGrpCat.{z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    (K : RingedSite.Hom.ModuleDerived.{z} X) (q : ℤ) :
    IsIsomorphic
      ((presheafToSheaf X.siteTopology AddCommGrpCat.{z}).obj
        (cohomologyPresheaf X K q))
      (underlyingCohomologySheaf X K q) := sorry

end RingedSite.Hom.ModuleDerived

namespace RingedSiteCohomology

/- The notation keeps the source-facing formulas short while all owners remain in
`RingedSite.Hom.ModuleDerived`. -/
@[inherit_doc RingedSite.Hom.ModuleDerived.cohomologyPresheaf]
scoped[RingedSiteCohomology] notation3:max "𝓗'[" q:max "](" X ", " K ")" =>
  RingedSite.Hom.ModuleDerived.cohomologyPresheaf X K q

@[inherit_doc RingedSite.Hom.ModuleDerived.cohomologySheaf]
scoped[RingedSiteCohomology] notation3:max "𝓗[" q:max "](" X ", " K ")" =>
  RingedSite.Hom.ModuleDerived.cohomologySheaf X K q

@[inherit_doc RingedSite.Hom.ModuleDerived.cohomologyOverObject]
scoped[RingedSiteCohomology] notation3:max "H^" q:max "(" U ", " K ")" =>
  RingedSite.Hom.ModuleDerived.cohomologyOverObject _ U K q

end RingedSiteCohomology
