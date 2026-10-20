/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup.CompactOpen

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 39.7.14: a group scheme with finitely many geometric connected components has a
quasi-compact open and closed subgroup scheme. -/
@[stacks 047V] #check
  (AlgebraicGeometry.GroupScheme.existsCompactClopenSubgroup_of_finiteGeometricComponents :
    ∀ {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G]
      [Finite (ConnectedComponents
        (FieldExtension.baseChange k (AlgebraicClosure k) G.hom))],
      ∃ H : Scheme.ClosedSubgroup G,
        IsOpenImmersion H.inclusion.left ∧
          let X := H.left.X
          CompactSpace X.left)
