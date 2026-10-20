/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Abelian sheafification on slices of an opens site

The opens site of a topological space and its first two slice levels have the standard
`AddCommGrpCat` sheafification and local-bijectivity instances.  These are topology facts, so
they do not depend on a chosen ring sheaf. The coefficient universe contains the space
universe, as in the canonical sheafification on the unsliced opens site.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u w

namespace TopCat

/-- Abelian-group-valued weak sheafification is available on every slice of an opens site,
with coefficients in a universe containing the space. -/
instance addCommGrpHasWeakSheafifyOver (X : TopCat.{u}) :
    ∀ U : Opens X,
      HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{max u w} := sorry

/-- Local bijectivity for abelian-group-valued presheaves is detected on every slice of an
opens site in a coefficient universe containing the space. -/
instance addCommGrpWEqualsLocallyBijectiveOver (X : TopCat.{u}) :
    ∀ U : Opens X,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{max u w} := sorry

/-- Abelian-group-valued weak sheafification is available on every twice-sliced opens site,
with coefficients in a universe containing the space. -/
instance addCommGrpHasWeakSheafifyOverOver (X : TopCat.{u}) :
    ∀ (U : Opens X) (V : Over U),
      HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V)
        AddCommGrpCat.{max u w} := sorry

/-- Local bijectivity for abelian-group-valued presheaves is detected on every twice-sliced
opens site in a coefficient universe containing the space. -/
instance addCommGrpWEqualsLocallyBijectiveOverOver (X : TopCat.{u}) :
    ∀ (U : Opens X) (V : Over U),
      (((Opens.grothendieckTopology X).over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{max u w} := sorry

end TopCat

