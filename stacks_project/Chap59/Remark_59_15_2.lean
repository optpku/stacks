/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineRefinement

open CategoryTheory AlgebraicGeometry

universe u v

/- Remark 59.15.2: fp denotes fidèlement plat (faithfully flat), while qc
denotes the finite affine-refinement condition. Joint surjectivity follows
from affine refinement alone, so no flatness hypothesis is needed. -/
@[stacks 03NX] #check (AlgebraicGeometry.Scheme.jointlySurjective_of_affineRefinement :
  {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
    (domains : ι → AlgebraicGeometry.Scheme.{u}) →
      (maps : ∀ index, domains index ⟶ T) →
        (∀ targetOpen : T.Opens, IsAffineOpen targetOpen →
          ∃ count : ℕ, ∃ indices : Fin count → ι,
            ∃ sourceOpens : (position : Fin count) →
              (domains (indices position)).Opens,
              (∀ position, IsAffineOpen (sourceOpens position)) ∧
                (⋃ position, maps (indices position) ''
                  (sourceOpens position : Set (domains (indices position)))) =
                  (targetOpen : Set T)) →
          ∀ point : T, ∃ index : ι, ∃ preimage : domains index,
            maps index preimage = point)
