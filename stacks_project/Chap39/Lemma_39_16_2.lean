/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.GroupScheme.Action.Module.Quasicoherent.ChangeBase
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 39.16.2: The identity-on-module-and-linearization rule gives an equivalence between
equivariant quasi-coherent modules and quasi-coherent modules on the associated action
groupoid. -/
@[stacks 03LL] #check
  (AlgebraicGeometry.Scheme.QCoh.Equivariant.actionGroupoidEquivalence :
    {S : Scheme.{u}} → (Y : Over S) → (G : Grp (Over Y.left)) →
      (X : AlgebraicGeometry.GroupScheme.Action G) →
        CategoryTheory.Equivalence (Scheme.QCoh.Equivariant G X)
          (AlgebraicGeometry.GroupoidScheme.QCoh
            (AlgebraicGeometry.GroupoidScheme.action Y G X)))
