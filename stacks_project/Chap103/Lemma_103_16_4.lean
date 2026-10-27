/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.WeakSerre

/-!
# Lemma 103.16.4

On an algebraic stack, quasi-coherent modules on the lisse-étale site form a
weak Serre subcategory of all lisse-étale modules, and likewise on the
flat-fppf site.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty

universe u

/- Lemma 103.16.4 (1): quasi-coherent modules on the lisse-étale site of an
algebraic stack form a weak Serre subcategory of all modules on that site. -/
@[stacks 07B4] #check
  (AlgebraicGeometry.AlgebraicStack.lisseEtaleQCoh.isWeakSerreClass :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      (AlgebraicGeometry.AlgebraicStack.lisseEtaleQuasiCoherent X).IsWeakSerreClass)

/- Lemma 103.16.4 (2): quasi-coherent modules on the flat-fppf site of an
algebraic stack form a weak Serre subcategory of all modules on that site. -/
@[stacks 07B4] #check
  (AlgebraicGeometry.AlgebraicStack.flatFppfQCoh.isWeakSerreClass :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      (AlgebraicGeometry.AlgebraicStack.flatFppfQuasiCoherent X).IsWeakSerreClass)
