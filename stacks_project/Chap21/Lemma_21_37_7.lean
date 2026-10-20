/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.BaseChange.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange.OfSites
public import ReasLib.CategoryTheory.Sites.BeckChevalley
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.37.7

The source item has two independent clauses and is therefore recalled with tags `(1)` and `(2)`.
Its site-facing data are a commutative square presented by
`u : 𝒞 ⥤ 𝒟`, `u' : 𝒞' ⥤ 𝒟'`, `v : 𝒟' ⥤ 𝒟`, and `v' : 𝒞' ⥤ 𝒞`, where `u` and `u'` are
continuous, `v` and `v'` are cocontinuous, and `v` and `v'` are also continuous.  The two
structure-sheaf conditions are inverse-image identifications; they are not pushforward equalities
and are not represented here by `IsFlat` assumptions.

The reusable owners are deliberately split by layer:

* the site square and its direct-image comparison are owned by `CatCommSq` and
  `CatCommSq.BeckChevalley`;
* the two inverse-image structure-sheaf identifications from the source have a reusable
  module-level bridge in `RingedSite.Hom.PullbackPresentation`, whose `baseChangeIso` and
  `lowerShriekIso` consume an explicit presentation; and
* the bounded and unbounded derived maps are the generic right-derived square map and the
  canonical ringed-site mate, respectively.  Their `IsIso` certificates remain separate Prop
  inputs/consequences, so no source hypothesis is silently replaced by finality or by flatness.

No cofinality hypothesis is added to either clause: cofinality is the extra hypothesis in Lemma
`21.37.6`, not in this source item.  In particular, the chapter file does not manufacture a
`Classical.choice` of an `IsIsomorphic` proof or install a global `IsIso` instance.
-/

open CategoryTheory

/- Lemma 21.37.7 (0FN7) (1): the site square and bounded-below base change. -/
@[stacks 0FN7 "(1), site square owner"]
#check @CategoryTheory.CatCommSq

@[stacks 0FN7 "(1), site direct-image comparison"]
#check @CategoryTheory.CatCommSq.BeckChevalley.comparison

@[stacks 0FN7 "(1), structure-sheaf pullback presentation"]
#check @RingedSite.Hom.PullbackPresentation

@[stacks 0FN7 "(1), module-linear square presentation"]
#check @RingedSite.Hom.FinalSquare.ModuleLift

@[stacks 0FN7 "(1), module direct-image base-change isomorphism"]
#check @RingedSite.Hom.PullbackPresentation.baseChangeIso

@[stacks 0FN7 "(1), module direct-image base-change map"]
#check @RingedSite.Hom.PullbackPresentation.comparison

@[stacks 0FN7 "(1), bounded-below right-derived square map"]
#check @CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square.map

@[stacks 0FN7 "(1), bounded-below right-derived square isomorphism criterion"]
#check @CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square.map_isIso

@[stacks 0FN7 "(1), bounded-below module base-change map"]
#check @RingedSite.Hom.DerivedBaseChange.BoundedBelow.map

@[stacks 0FN7 "(1), exact-horizontal bounded-below base-change map"]
#check @CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square.Exact.map

@[stacks 0FN7 "(1), exact-horizontal bounded-below isomorphism transport"]
#check @CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square.Exact.map_isIso

@[stacks 0FN7 "(1), bounded-below module base-change component"]
#check @RingedSite.Hom.DerivedBaseChange.BoundedBelow.app

@[stacks 0FN7 "(1), strict-square module bridge"]
#check @RingedSite.Hom.DerivedBaseChange.BoundedBelow.mapOfCommSq

/- Lemma 21.37.7 (0FN7) (2): the unbounded derived base-change transformation and its
exact lower-shriek bridge. -/
@[stacks 0FN7 "(2), lower-shriek base-change isomorphism"]
#check @RingedSite.Hom.PullbackPresentation.lowerShriekIso

@[stacks 0FN7 "(2), exact lower-shriek criterion"]
#check @CategoryTheory.Functor.AbelianLowerShriek.exact_of_isRightAdjoint

@[stacks 0FN7 "(2), unbounded derived base-change source"]
#check @RingedSite.Hom.DerivedBaseChange.source

@[stacks 0FN7 "(2), unbounded derived base-change target"]
#check @RingedSite.Hom.DerivedBaseChange.target

@[stacks 0FN7 "(2), unbounded derived base-change natural transformation"]
#check @RingedSite.Hom.DerivedBaseChange.mapNatTrans

@[stacks 0FN7 "(2), unbounded derived base-change mate specification"]
#check @RingedSite.Hom.DerivedBaseChange.mapNatTrans_isMap

@[stacks 0FN7 "(2), unbounded derived base-change component bridge"]
#check @RingedSite.Hom.DerivedBaseChange.mapNatTrans_app_eq_map

@[stacks 0FN7 "(2), derived transport of the comparison"]
#check @CategoryTheory.Functor.RightDerived.natIsoOfIso

@[stacks 0FN7 "(2), bounded-below derived isomorphism transport"]
#check @CategoryTheory.Functor.RightDerived.Bounded.map_isIso
