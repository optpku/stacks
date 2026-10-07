module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.UnderlyingComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology after forgetting module scalars

This file owns the cohomology-group consequences of the derived comparison between module global
sections and global sections of the underlying additive sheaf.  The localized statement combines
the global comparison on the slice site with the canonical restriction to that slice.
@stack 091E
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Abelian.Ext

noncomputable section

universe u v

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]
variable {R : Sheaf J RingCat.{max u v}}

namespace SheafOfModules.Cohomology

/-- Lemma 21.12.4 (1): global cohomology of the underlying additive sheaf of an `R`-module
sheaf is isomorphic to `Ext` from the unit `R`-module. -/
@[stacks 03FD, stacks 091E "global underlying-module cohomology comparison"]
theorem underlying_isomorphic
    [HasExt (SheafOfModules R)] (F : SheafOfModules R) (i : ℕ) :
    IsIsomorphic
      (AddCommGrpCat.of (((SheafOfModules.toSheaf R).obj F).H i))
      (AddCommGrpCat.of (Ext (SheafOfModules.unit R) F i)) := sorry

/-- Lemma 21.12.4 (2): cohomology over `U` of the underlying additive sheaf of an `R`-module
sheaf is isomorphic to `Ext` from the unit module on the localized ringed site. -/
@[stacks 03FD "localized underlying-module cohomology comparison"]
theorem underlyingOver_isomorphic
    (U : C)
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify (J.over U) AddCommGrpCat.{max u v}]
    [HasExt (Sheaf (J.over U) AddCommGrpCat.{max u v})]
    [HasExt (SheafOfModules (R.over U))]
    (F : SheafOfModules R) (i : ℕ) :
    IsIsomorphic
      (((SheafOfModules.toSheaf R).obj F).H' i U)
      (AddCommGrpCat.of
        (Ext (SheafOfModules.unit (R.over U)) (F.over U) i)) := sorry

/-!
The following two declarations are source-facing degree-one views.  The all-degree comparison
above is the reusable core, while these views keep the two textbook orientations visible without
choosing an inverse from a proposition.  The actual derived natural-isomorphism data lives in
`RingedSite.Hom.ModuleSections.globalIso`.
-/

/-- Lemma 21.5.1 (03F1): the degree-one extension class and the cohomology class of a module
sheaf are identified after forgetting to additive sheaves. -/
@[stacks 03F1 "degree-one Ext/cohomology comparison"]
theorem ext_isomorphic_underlyingCohomology_one
    (R : Sheaf J RingCat.{max u v})
    [HasExt (SheafOfModules R)]
    (F : SheafOfModules R) :
    IsIsomorphic
      (AddCommGrpCat.of (Ext (SheafOfModules.unit R) F 1))
      (AddCommGrpCat.of (((SheafOfModules.toSheaf R).obj F).H 1)) := sorry

/-- Lemma 21.5.2 (03F2): first cohomology is unchanged by forgetting the module structure. -/
@[stacks 03F2 "underlying/module degree-one cohomology comparison"]
theorem underlyingCohomology_isomorphic_ext_one
    (R : Sheaf J RingCat.{max u v})
    [HasExt (SheafOfModules R)]
    (F : SheafOfModules R) :
    IsIsomorphic
      (AddCommGrpCat.of (((SheafOfModules.toSheaf R).obj F).H 1))
      (AddCommGrpCat.of (Ext (SheafOfModules.unit R) F 1)) := sorry

/-- The underlying additive and module-valued first-cohomology functors are isomorphic as
functors.  This is the reusable functorial view of Lemma 21.5.2; it deliberately remains a
proposition until a canonical natural-isomorphism construction is available. -/
@[stacks 03F2 "functorial degree-one cohomology comparison"]
theorem underlyingCohomologyFunctor_isomorphic_extFunctor_one
    (R : Sheaf J RingCat.{max u v})
    [HasExt (SheafOfModules R)] :
    IsIsomorphic
      (SheafOfModules.toSheaf R ⋙ Sheaf.functorH J 1)
      (Abelian.extFunctorObj (SheafOfModules.unit R) 1) := sorry

end SheafOfModules.Cohomology
