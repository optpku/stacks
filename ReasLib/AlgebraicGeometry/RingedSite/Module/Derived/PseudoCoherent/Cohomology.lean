/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalProperties
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology of pseudo-coherent derived module sheaves

The highest potentially nonzero cohomology sheaves of an `m`-pseudo-coherent object satisfy the
expected finite-generation and finite-presentation bounds.
-/

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open RingedSite.Hom (ModuleDerived)

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived.IsMPseudoCoherent

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {K : ModuleDerived.{w} X} {m : ℤ}

/-- Lemma 21.45.7 (1): the top cohomology sheaf of an `m`-pseudo-coherent object in
`D^{≤ m}` is of finite type. -/
@[stacks 08FX "(1)"]
theorem topCohomology_isFiniteType
    (hK : K.IsMPseudoCoherent m) (hLE : K.IsLE m) :
    (cohomologySheaf X K m).IsFiniteType := sorry

/-- Lemma 21.45.7 (2): degree `m + 1` cohomology of an `m`-pseudo-coherent object in
`D^{≤ m + 1}` is finitely presented. -/
@[stacks 08FX "(2)"]
theorem nextCohomology_isFinitePresentation
    (hK : K.IsMPseudoCoherent m) (hLE : K.IsLE (m + 1)) :
    (cohomologySheaf X K (m + 1)).IsFinitePresentation := sorry

end RingedSite.Hom.ModuleDerived.IsMPseudoCoherent
