/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocallyGiven.Gluing
import StacksCheckRecall

/-!
# BBD gluing for locally given derived modules

A morphism of sites preserving equalizers and pullbacks and a full subcategory
covering its source allow uniformly bounded below local derived modules with
vanishing negative self-Exts to glue uniquely.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite RingedSite.ModuleDerived RingedSite.ModuleDerived.LocallyGiven
open scoped SemiRepresentableFamily

universe ιfam u v w uB vB u' v'

/- Lemma 85.24.3 (BBD glueing lemma)
Under the site, covering, negative self-Ext, and uniform boundedness hypotheses,
a solution exists and is unique up to unique compatible isomorphism. -/
@[stacks 0DCB] #check (RingedSite.ModuleDerived.LocallyGiven.exists_solution :
  ∀ {X : RingedSite.{u, v, w}}
    [HasEqualizers X.carrier] [HasPullbacks X.carrier]
    {B : Type uB} [Category.{vB} B] [h_univLE : UnivLE.{max u v, w}]
    (D : LocallyGiven.{u, v, w, w, uB, vB} X B)
    {C' : Type u'} [Category.{v'} C'] [HasEqualizers C'] [HasPullbacks C']
    (J' : GrothendieckTopology C') (u' : C' ⥤ X)
    [IsMorphismOfSites J' X.siteTopology u']
    [PreservesLimitsOfShape WalkingParallelPair u']
    [PreservesLimitsOfShape WalkingCospan u']
    (ι : B ⥤ C') [ι.Full] [ι.Faithful],
    D.u = ι ⋙ u' →
    (∀ W : C', ∃ 𝒰 : FormalCoproduct.{ιfam} (Over W),
      𝒰.IsBasisCovering J'.toPrecoverage (Set.range ι.obj)) →
    negativeSelfExt h_univLE D → uniformlyBoundedBelow D →
    Nonempty (Solution D))

#check (RingedSite.ModuleDerived.LocallyGiven.unique_hom_solution :
  ∀ {X : RingedSite.{u, v, w}}
    [HasEqualizers X.carrier] [HasPullbacks X.carrier]
    {B : Type uB} [Category.{vB} B] [h_univLE : UnivLE.{max u v, w}]
    (D : LocallyGiven.{u, v, w, w, uB, vB} X B)
    {C' : Type u'} [Category.{v'} C'] [HasEqualizers C'] [HasPullbacks C']
    (J' : GrothendieckTopology C') (u' : C' ⥤ X)
    [IsMorphismOfSites J' X.siteTopology u']
    [PreservesLimitsOfShape WalkingParallelPair u']
    [PreservesLimitsOfShape WalkingCospan u']
    (ι : B ⥤ C') [ι.Full] [ι.Faithful],
    D.u = ι ⋙ u' →
    (∀ W : C', ∃ 𝒰 : FormalCoproduct.{ιfam} (Over W),
      𝒰.IsBasisCovering J'.toPrecoverage (Set.range ι.obj)) →
    negativeSelfExt h_univLE D → uniformlyBoundedBelow D →
    ∀ S S' : Solution D, ∃ e : S.obj ≅ S'.obj,
      Solution.IsCompatibleIso S S' e ∧
        ∀ e' : S.obj ≅ S'.obj, Solution.IsCompatibleIso S S' e' → e'.hom = e.hom)
