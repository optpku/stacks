/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Relocalization
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localizing a morphism of ringed sites at an arrow

A morphism of ringed sites `f : X ⟶ Y`, an object `V : Y`, and an arrow
`c : U ⟶ f.base.obj V` determine a morphism of localized ringed topoi.  The construction is
kept as the explicit composite of relocalization with the canonical localized site morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : X.Hom Y) (V : Y)
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vY vX, w}]

/-- The morphism of ringed topoi presented by localizing `f` at `V`. -/
@[stacks 04J1 "localized site factor"]
noncomputable def localizationToposHom :
    ToposHom (X.localization (f.base.obj V)) (Y.localization V) :=
  (localization f V).toToposHom

section At

variable {U : X} (c : U ⟶ f.base.obj V)
-- These ambient instances select the slice instances inherited via `J.over`; they do not become
-- parameters of `localizationAt`, whose public API only needs the universe bounds above.
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- Lemma 18.20.2 (04J1): the localized morphism `f_c`, defined as relocalization along `c`
followed by the morphism obtained by localizing `f` at `V`. -/
@[stacks 04J1 "localized morphism"]
noncomputable def localizationAt :
    ToposHom (X.localization U) (Y.localization V) :=
  ToposHom.comp (Localization.relocalization X c) (localizationToposHom f V)

end At

-- Both owners are explicit composites of canonical direct-image functors and structure maps;
-- their only `sorryAx` dependencies may come from Prop-valued exactness/site hypotheses.

end RingedSite.Hom
