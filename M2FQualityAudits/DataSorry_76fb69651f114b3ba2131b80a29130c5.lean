module

import Lean

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.RingedTopos
public import ReasLib.CategoryTheory.Sites.Derived.SectionsComparison
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Exactness
public import ReasLib.CategoryTheory.Sites.Cohomology.SectionsComparison
public import ReasLib.CategoryTheory.Sites.Over.Derived.Unbounded
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open AlgebraicGeometry.StandardTopology.Big
open ComplexShape
open Functor.RightDerived
open RingedSite.Hom.ModuleSections.Underlying

noncomputable section

universe u

/-!
The six comparisons in Lemma 59.99.3 are recorded as objectwise isomorphisms in the
derived category of abelian groups.  The ordinary clauses use the site-derived sections owners;
the module clauses use the canonical ringed-site derived categories and explicit functors for the
corresponding pullback and sections operations.
-/

/-- The terminal object of the small étale site of a scheme. -/
noncomputable def smallEtaleTerminal (S : Scheme.{u}) : S.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 S) inferInstance

/-- The chosen terminal object of the small étale site is terminal. -/
noncomputable def smallEtaleTerminal_isTerminal (S : Scheme.{u}) :
    Limits.IsTerminal (smallEtaleTerminal S) :=
  MorphismProperty.Over.mkIdTerminal @Etale S

/-- The standard étale topology is distinct from the Zariski topology. -/
theorem etale_ne_zariski : StandardTopology.etale ≠ StandardTopology.zariski := sorry

/-- The exact additive derived inverse image presented by `siteMorphismOfTopoi S`. -/
noncomputable def piAbelianInverseImageDerived (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))] :
    DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory
        (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) :=
  let F := (relocalizationFunctor (𝟙 S)).sheafPullback
    AddCommGrpCat.{u} S.smallEtaleTopology
    (S.overGrothendieckTopology @Etale)
  -- Local instance justification (proof-local temporary data): expose the exactness
  -- components returned by `abelianPullback_exact` to the derived-category constructor.
  letI : PreservesFiniteLimits F :=
    (Functor.IsMorphismOfSites.abelianPullback_exact
      (relocalizationFunctor (𝟙 S))).1
  -- Local instance justification (proof-local temporary data): expose the exactness
  -- components returned by `abelianPullback_exact` to the derived-category constructor.
  letI : PreservesFiniteColimits F :=
    (Functor.IsMorphismOfSites.abelianPullback_exact
      (relocalizationFunctor (𝟙 S))).2
  F.mapDerivedCategory

/-- The exact additive derived inverse image presented by `smallMorphism f`. -/
noncomputable def smallEtaleAbelianInverseImageDerived
    {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((smallEtalePullback f).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          (T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}))] :
    DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) :=
  let F := (smallEtalePullback f).sheafPullback
    AddCommGrpCat.{u} S.smallEtaleTopology T.smallEtaleTopology
  -- Local instance justification (proof-local temporary data): expose the exactness
  -- components returned by `abelianPullback_exact` to the derived-category constructor.
  letI : PreservesFiniteLimits F :=
    (Functor.IsMorphismOfSites.abelianPullback_exact
      (smallEtalePullback f)).1
  -- Local instance justification (proof-local temporary data): expose the exactness
  -- components returned by `abelianPullback_exact` to the derived-category constructor.
  letI : PreservesFiniteColimits F :=
    (Functor.IsMorphismOfSites.abelianPullback_exact
      (smallEtalePullback f)).2
  F.mapDerivedCategory

/-- Lemma 59.99.3 (1): cohomology of the inverse image from the small étale
site to the big étale site agrees with cohomology on `Sₑₜ`. -/
@[stacks 0DDH]
theorem etaleCohomology_piInverseImage
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))]
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived (S.overGrothendieckTopology @Etale)
          (Over.mk (𝟙 S))).obj
            ((piAbelianInverseImageDerived S).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived S.smallEtaleTopology
          (smallEtaleTerminal S)).obj K)) := sorry

/-- Lemma 59.99.3 (2): the corresponding comparison for derived modules on
the small étale site. -/
@[stacks 0DDH]
theorem etaleModuleCohomology_piPullback
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [(Scheme.SiteRestriction.bigToEtale .etale S etale_ne_zariski).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u + 1}
        (Scheme.SiteRestriction.bigToEtale .etale S etale_ne_zariski))
      (RingedSite.Hom.ModuleQis.{u + 1}
        (Small.ringedSite S))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1} (Small.ringedSite S))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1}
        (StandardTopology.Big.ringedSite .etale S))]
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (Small.ringedSite S)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (StandardTopology.Big.ringedSite .etale S) (Over.mk (𝟙 S))).obj
          ((RingedSite.Hom.modulePullbackDerived.{u + 1}
            (Scheme.SiteRestriction.bigToEtale .etale S etale_ne_zariski)).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (Small.ringedSite S) (smallEtaleTerminal S)).obj K)) := sorry

/-- Lemma 59.99.3 (3): ordinary étale cohomology commutes with the
small-site inverse image attached to `f`. -/
@[stacks 0DDH]
theorem etaleCohomology_smallInverseImage
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((smallEtalePullback f).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          (T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}))]
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived (S.overGrothendieckTopology @Etale)
          (Over.mk f)).obj
            ((piAbelianInverseImageDerived S).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived T.smallEtaleTopology
          (smallEtaleTerminal T)).obj
            ((smallEtaleAbelianInverseImageDerived f).obj K))) := sorry

/-- Lemma 59.99.3 (4): module-valued étale cohomology commutes with the
derived small-site pullback attached to `f`. -/
@[stacks 0DDH]
theorem etaleModuleCohomology_smallPullback
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [(Scheme.SiteRestriction.bigToEtale .etale S etale_ne_zariski).modulePushforward.{u + 1}.IsRightAdjoint]
    [(Small.ringedHom f).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u + 1}
        (Scheme.SiteRestriction.bigToEtale .etale S etale_ne_zariski))
      (RingedSite.Hom.ModuleQis.{u + 1}
        (Small.ringedSite S))]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived.{u + 1}
        (Small.ringedHom f))
      (RingedSite.Hom.ModuleQis.{u + 1}
        (Small.ringedSite S))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1} (Small.ringedSite T))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1}
        (StandardTopology.Big.ringedSite .etale S))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat.{u + 1} (Small.ringedSite S))]
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (Small.ringedSite S)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (StandardTopology.Big.ringedSite .etale S) (Over.mk f)).obj
          ((RingedSite.Hom.modulePullbackDerived.{u + 1}
            (Scheme.SiteRestriction.bigToEtale .etale S etale_ne_zariski)).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (Small.ringedSite T) (smallEtaleTerminal T)).obj
          ((RingedSite.Hom.modulePullbackDerived.{u + 1}
            (Small.ringedHom f)).obj K))) := sorry

/-- Lemma 59.99.3 (5): for a derived big-site object `M`, cohomology over
`T` agrees with cohomology on `Tₑₜ` after relocalization. -/
@[stacks 0DDH]
theorem etaleCohomology_relocalization
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    (M : DerivedCategory
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived (S.overGrothendieckTopology @Etale)
          (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((siteAbelianSectionsDerived T.smallEtaleTopology
          (smallEtaleTerminal T)).obj
          ((siteAbelianInverseImageDerived T.smallEtaleTopology
            (S.overGrothendieckTopology @Etale)
            (relocalizationFunctor f)).obj M))) := sorry

/-- Lemma 59.99.3 (6): the module-valued relocalization comparison for
the big étale site and the small étale site of `T`. -/
@[stacks 0DDH]
theorem etaleModuleCohomology_relocalization
    {S T : Scheme.{u}} (f : T ⟶ S) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [(SheafOfModules.restrictScalars
      (ringedToposHom f).structureMap).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (RingedSite.ToposHom.modulePullbackToDerived.{u + 1}
        (ringedToposHom f))
      (RingedSite.Hom.ModuleQis.{u + 1} (liftedRingedSite .etale S))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat (Small.liftedRingedSite T))]
    [IsGrothendieckAbelian
      (RingedSite.ModuleCat (liftedRingedSite .etale S))]
    (M : RingedSite.Hom.ModuleDerived
      (liftedRingedSite .etale S)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (liftedRingedSite .etale S) (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1}
          (Small.liftedRingedSite T) (smallEtaleTerminal T)).obj
          ((RingedSite.ToposHom.modulePullbackDerived.{u + 1}
            (ringedToposHom f)).obj M))) := sorry

end

end


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
