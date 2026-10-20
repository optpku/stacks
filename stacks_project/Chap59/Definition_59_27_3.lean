/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic

open AlgebraicGeometry CategoryTheory

universe u

variable (S : Scheme.{u})

/- Definition 59.27.3: the big and small étale and Zariski sites associated
to a scheme `S`. -/
@[stacks 03PI] #check
  (AlgebraicGeometry.Scheme.bigZariskiTopology S :
    GrothendieckTopology S.bigZariskiSite)

#check
  (AlgebraicGeometry.Scheme.smallZariskiTopology S :
    GrothendieckTopology S.smallZariskiSite)

#check
  (AlgebraicGeometry.Scheme.overGrothendieckTopology
    (P := @AlgebraicGeometry.Etale) S :
    GrothendieckTopology (Over S))

#check
  (AlgebraicGeometry.Scheme.smallEtaleTopology S :
    GrothendieckTopology S.Etale)
