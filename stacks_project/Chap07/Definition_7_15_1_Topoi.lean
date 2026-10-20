/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

/-!
# Definition 7.15.1 (Topoi)

The site-presented category of set-valued sheaves and its geometric morphisms
are owned by the reusable topos-morphism API.
-/

@[expose] public section

/- Definition 7.15.1 (Topoi) (00XA): a topos presented by a site is its
category of set-valued sheaves, and a morphism of such topoi is a left-exact
adjunction. -/
@[stacks 00XA] #check @CategoryTheory.MorphismOfTopoiIn

#check @CategoryTheory.MorphismOfTopoiIn.inverseImage_preservesFiniteLimits
#check @CategoryTheory.Functor.morphismOfTopoiInOfContinuous
