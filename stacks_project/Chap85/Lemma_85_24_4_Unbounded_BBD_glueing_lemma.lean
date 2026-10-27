/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocallyGiven.UnboundedGluing
import StacksCheckRecall

/-!
# Unbounded BBD gluing for locally given derived modules

Cohomology in a fiberwise weak Serre family and vanishing negative self-Exts
ensure existence and uniqueness of a global solution under the site and
covering hypotheses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite RingedSite.Hom RingedSite.Localization
open RingedSite.ModuleDerived RingedSite.ModuleDerived.LocallyGiven
open scoped SemiRepresentableFamily

universe ιfam wι u v w uB vB u' v'

/- Lemma 85.24.4 (Unbounded BBD glueing lemma)
Under the site, covering, negative self-Ext, and fiberwise Serre cohomology hypotheses,
a solution exists and is unique up to unique compatible isomorphism. -/
@[stacks 0DCC] #check (RingedSite.ModuleDerived.LocallyGiven.exists_solution_of_cohomologyIn :
  ∀ {X : RingedSite.{u, v, w}}
    [HasEqualizers X.carrier] [HasPullbacks X.carrier]
    {B : Type uB} [Category.{vB} B] [h_univLE : UnivLE.{max u v, w}]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ U : X, (X.siteTopology.over U).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ {U V : X} (f : V ⟶ U),
      (SheafOfModules.restrictScalars.{w} (relocalization X f).structureMap).IsRightAdjoint]
    (D : LocallyGiven.{u, v, w, w, uB, vB} X B)
    {C' : Type u'} [Category.{v'} C'] [HasEqualizers C'] [HasPullbacks C']
    (J' : GrothendieckTopology C') (u' : C' ⥤ X)
    [IsMorphismOfSites J' X.siteTopology u']
    [PreservesLimitsOfShape WalkingParallelPair u']
    [PreservesLimitsOfShape WalkingCospan u']
    (ι : B ⥤ C') [ι.Full] [ι.Faithful]
    (A : FiberwiseSerre.{wι, u, v, w} X),
    D.u = ι ⋙ u' →
    (∀ W : C', ∃ 𝒰 : FormalCoproduct.{ιfam} (Over W),
      𝒰.IsBasisCovering J'.toPrecoverage (Set.range ι.obj)) →
    negativeSelfExt h_univLE D → obj_mem_cohomologyIn D A →
    Nonempty (Solution D))

#check (RingedSite.ModuleDerived.LocallyGiven.unique_hom_solution_of_cohomologyIn :
  ∀ {X : RingedSite.{u, v, w}}
    [HasEqualizers X.carrier] [HasPullbacks X.carrier]
    {B : Type uB} [Category.{vB} B] [h_univLE : UnivLE.{max u v, w}]
    [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ U : X, (X.siteTopology.over U).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    [∀ {U V : X} (f : V ⟶ U),
      (SheafOfModules.restrictScalars.{w} (relocalization X f).structureMap).IsRightAdjoint]
    (D : LocallyGiven.{u, v, w, w, uB, vB} X B)
    {C' : Type u'} [Category.{v'} C'] [HasEqualizers C'] [HasPullbacks C']
    (J' : GrothendieckTopology C') (u' : C' ⥤ X)
    [IsMorphismOfSites J' X.siteTopology u']
    [PreservesLimitsOfShape WalkingParallelPair u']
    [PreservesLimitsOfShape WalkingCospan u']
    (ι : B ⥤ C') [ι.Full] [ι.Faithful]
    (A : FiberwiseSerre.{wι, u, v, w} X),
    D.u = ι ⋙ u' →
    (∀ W : C', ∃ 𝒰 : FormalCoproduct.{ιfam} (Over W),
      𝒰.IsBasisCovering J'.toPrecoverage (Set.range ι.obj)) →
    negativeSelfExt h_univLE D → obj_mem_cohomologyIn D A →
    ∀ S S' : Solution D, ∃ e : S.obj ≅ S'.obj,
      Solution.IsCompatibleIso S S' e ∧
        ∀ e' : S.obj ≅ S'.obj, Solution.IsCompatibleIso S S' e' → e'.hom = e.hom)
