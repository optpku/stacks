/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf.H

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Over.GlobalSections.functor_isRepresentable :
  ∀ (S : AlgebraicGeometry.Scheme.{u}),
    (AlgebraicGeometry.Scheme.Over.GlobalSections.functor S).IsRepresentable)

#check (AlgebraicGeometry.Scheme.Site.structurePresheaf_not_isSheaf_hTopology :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) [Nonempty S],
    ¬ Presieve.IsSheaf
      ((AlgebraicGeometry.Scheme.hPrecoverage.toGrothendieck).over S)
      (AlgebraicGeometry.Scheme.Over.GlobalSections.functor S))

/- Example 38.35.2: on schemes over a nonempty base `S`, the h topology is not
subcanonical. The underlying structure presheaf is represented by `𝔸¹_S` but is not a sheaf. -/
@[stacks 0EV1] #check (AlgebraicGeometry.Scheme.hTopology_not_subcanonical :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) [Nonempty S],
    ¬ ((AlgebraicGeometry.Scheme.hPrecoverage.toGrothendieck).over S).Subcanonical)
