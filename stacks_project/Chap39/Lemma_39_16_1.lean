/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.GroupoidScheme.Action
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 39.16.1: a group scheme action determines its action groupoid over the base. -/
@[stacks 0234] #check (AlgebraicGeometry.GroupoidScheme.action :
  {S : Scheme.{u}} → (Y : Over S) → (G : Grp (Over Y.left)) →
    AlgebraicGeometry.GroupScheme.Action G → AlgebraicGeometry.GroupoidScheme S)
