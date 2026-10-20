/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Canonical
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.80.2: the scheme `Spec ℤ` is not a quasi-compact object of
`Sheaf.canonicalTopology Scheme`. This is the site-object property
`GrothendieckTopology.QuasiCompactObject`, not topological quasi-compactness of
the underlying space of `Spec ℤ`. -/
@[stacks 0EUG] #check (AlgebraicGeometry.specInt_not_quasiCompactObject :
    ¬ (CategoryTheory.Sheaf.canonicalTopology AlgebraicGeometry.Scheme.{u}).QuasiCompactObject
      (AlgebraicGeometry.Spec (.of (ULift.{u} ℤ))))
