/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 96.4.2: associated-site notation such as 𝒳_étale is used only for
categories fibred in groupoids. Roman X_étale denotes the small étale site of
a scheme or algebraic space; this convention avoids confusing the two
presentations. -/
@[stacks 06TQ] #check (AlgebraicGeometry.GroupoidsOver.etaleTopology :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    CategoryTheory.GrothendieckTopology X.total)
#check (AlgebraicGeometry.Scheme.smallEtaleTopology :
  ∀ (X : AlgebraicGeometry.Scheme.{u}),
    CategoryTheory.GrothendieckTopology X.Etale)
#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleTopology :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.GrothendieckTopology
      (AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X))
