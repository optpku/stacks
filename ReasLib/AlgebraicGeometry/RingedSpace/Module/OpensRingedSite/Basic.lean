/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Topology.Sheaves.Abelian.Over
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The opens ringed site of a ringed space

This file owns the canonical ringed site of open subsets and the sheafification instances on its
localizations.  It deliberately stays below both complex and derived module infrastructure.
-/

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The commutative ringed site of opens of a ringed space, equipped with its structure sheaf. -/
@[stacks 03DF "opens ringed site"]
abbrev opensRingedSite (X : RingedSpace.{u}) :=
  RingedSite.ofCommRingSheaf (Opens.grothendieckTopology X) X.sheaf

namespace OpensRingedSite

-- Expose the definitionally equal slice topology directly. The certificates below
-- then depend only on the opens site, not on the category structure on ringed sites.

/-- Abelian-group-valued weak sheafification is available uniformly on localizations of the
opens ringed site of a ringed space. -/
@[stacks 03DF "abelian sheafification on localized opens sites"]
instance localizationHasWeakSheafify (X : RingedSpace.{u, u}) :
    ∀ U : TopologicalSpace.Opens X,
      HasWeakSheafify ((Opens.grothendieckTopology X).over U)
        AddCommGrpCat.{u} := by
  intro U
  exact TopCat.addCommGrpHasWeakSheafifyOver.{u, 0} (TopCat.of X) U

/-- Local bijectivity on every localization of an opens ringed site agrees with the weak
equivalences used by sheafification. -/
@[stacks 03DF "local bijectivity on localized opens sites"]
instance localizationWEqualsLocallyBijective (X : RingedSpace.{u, u}) :
    ∀ U : TopologicalSpace.Opens X,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := by
  intro U
  exact TopCat.addCommGrpWEqualsLocallyBijectiveOver.{u, 0} (TopCat.of X) U

/-- Abelian-group-valued weak sheafification is available uniformly after two successive
localizations of an opens ringed site. -/
@[stacks 03DF "abelian sheafification on iterated localized opens sites"]
instance iteratedLocalizationHasWeakSheafify (X : RingedSpace.{u, u}) :
    ∀ (U : TopologicalSpace.Opens X) (V : Over U),
      HasWeakSheafify (((Opens.grothendieckTopology X).over U).over V)
        AddCommGrpCat.{u} := by
  intro U V
  exact TopCat.addCommGrpHasWeakSheafifyOverOver.{u, 0} (TopCat.of X) U V

/-- Local bijectivity after two successive localizations of an opens ringed site agrees with
the weak equivalences used by sheafification. -/
@[stacks 03DF "local bijectivity on iterated localized opens sites"]
instance iteratedLocalizationWEqualsLocallyBijective (X : RingedSpace.{u, u}) :
    ∀ (U : TopologicalSpace.Opens X) (V : Over U),
      (((Opens.grothendieckTopology X).over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := by
  intro U V
  exact TopCat.addCommGrpWEqualsLocallyBijectiveOverOver.{u, 0} (TopCat.of X) U V

end OpensRingedSite

end AlgebraicGeometry.RingedSpace

