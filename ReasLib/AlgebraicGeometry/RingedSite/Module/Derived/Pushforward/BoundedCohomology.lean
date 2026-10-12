/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Hom.BoundedCohomologyBasis
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.Abelian.Functor.CohomologicalDimension
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyInProperty
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Tower
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.BoundedCohomologyBasis
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-cohomology control for derived direct image

This leaf owns the reusable ringed-site interface behind Lemmas 21.25.4 and 21.25.6.  The
coefficient conditions are expressed by the relative right-derived predicates
`Functor.MapsRightDerived` and `Functor.HasCohomologicalDimensionLEOn`; their objectwise forms are
available from the corresponding `_iff` lemmas.  Thus the source-facing assumptions remain
visible without baking a chapter-specific higher-direct-image notation into the core API.

The site carrier and morphism universes of `X` and `Y` are independent.  Coefficients live in
`max z vX vY`, the smallest symmetric universe expression allowing objectwise cohomology on both
sites.  The only remaining size assumptions are the canonical `UnivLE` constraints required by
the derived module categories.
-/

open CategoryTheory CategoryTheory.Limits
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

noncomputable section

universe wι uX vX uY vY w z

namespace RingedSite.Hom.modulePushforwardDerived

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : RingedSite.Hom X Y)
variable [UnivLE.{max uX vX, max z vX vY}]
variable [UnivLE.{max uY vY, max z vX vY}]
variable [HasInjectiveResolutions (ModuleCat.{max z vX vY} X)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{max z vX vY} f)
    (ModuleQis.{max z vX vY} X)]

/-- The derived direct-image map induced by the canonical lower truncation
`K ⟶ τ≥(-n) K`.  Its target is deliberately expressed through the reusable lower-truncation
tower, so later limit arguments can consume it without unfolding the truncation construction. -/
@[stacks 0D6U "derived pushforward lower-stage map"]
noncomputable abbrev lowerStageMap
    (K : ModuleDerived.{max z vX vY} X) (n : ℕ) :
    (modulePushforwardDerived.{max z vX vY} f).obj K ⟶
      (modulePushforwardDerived.{max z vX vY} f).obj
        ((DerivedCategory.Truncation.Lower.tower K).obj (Opposite.op n)) :=
  (modulePushforwardDerived.{max z vX vY} f).map
    (DerivedCategory.Truncation.Lower.toStage K n)

section Landing

variable [HasSheafify X.siteTopology AddCommGrpCat.{max z vX vY}]
variable [HasExt.{max z vX vY}
  (Sheaf X.siteTopology AddCommGrpCat.{max z vX vY})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max z vX vY}]
variable [HasExt.{max z vX vY}
  (Sheaf Y.siteTopology AddCommGrpCat.{max z vX vY})]
variable (A : ObjectProperty (ModuleCat.{max z vX vY} X))
variable (A' : ObjectProperty (ModuleCat.{max z vX vY} Y))
variable [ObjectProperty.IsWeakSerreClass A]
variable [ObjectProperty.IsWeakSerreClass A']

/-- Lemma 21.25.4 (0D6U), first clause: under bounded cohomology bases on both sites, the
right-derived direct image sends objects with cohomology in `A` to objects with cohomology in
`A'`.  The hypotheses `h_mem` and `h_vanish` are the canonical relative statements for all
higher direct images and for the uniform bound `N`, respectively. -/
@[stacks 0D6U]
theorem obj_mem_of_boundedBasis
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vX, vY, uY}
      Y.structureSheaf A')
    (N : ℤ)
    (h_mem : f.modulePushforward.{max z vX vY}.MapsRightDerived A A')
    (h_vanish :
      f.modulePushforward.{max z vX vY}.HasCohomologicalDimensionLEOn A N)
    (K : DerivedCategory.CohomologyIn A) :
    DerivedCategory.cohomologyIn A'
      ((modulePushforwardDerived.{max z vX vY} f).obj K.obj) := sorry

/-- Lemma 21.25.4 (0D6U), second clause: with the same two bounded-basis setups and the
higher-direct-image membership and vanishing hypotheses, the canonical map
`H^j(Rf_* K) ⟶ H^j(Rf_*(τ≥(-n) K))` is an isomorphism for `j ≥ N - n`. -/
@[stacks 0D6U]
theorem homologyMap_isIso_of_boundedBasis
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vX, vY, uY}
      Y.structureSheaf A')
    (N : ℤ)
    (h_mem : f.modulePushforward.{max z vX vY}.MapsRightDerived A A')
    (h_vanish :
      f.modulePushforward.{max z vX vY}.HasCohomologicalDimensionLEOn A N)
    (K : DerivedCategory.CohomologyIn A)
    (n : ℕ) (j : ℤ) (hj : N - (n : ℤ) ≤ j) :
    IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{max z vX vY} Y) j).map
        (lowerStageMap f K.obj n)) := sorry

end Landing

section PullbackBasis

variable [HasSheafify X.siteTopology AddCommGrpCat.{max z vX vY}]
variable [HasExt.{max z vX vY}
  (Sheaf X.siteTopology AddCommGrpCat.{max z vX vY})]
variable (A : ObjectProperty (ModuleCat.{max z vX vY} X))
variable [ObjectProperty.IsWeakSerreClass A]

/-- Lemma 21.25.6 (0D6W): if `X` has a bounded cohomology basis for `A` and `f` has the
pullback-basis property, then the lower-truncation comparison for `Rf_*` is an isomorphism in
every degree `j ≥ N - n` under the relative cohomological-dimension bound.  The pullback basis is
an explicit source datum: it records the local vanishing on target-site covers after pullback and
is not silently discarded as a redundant hypothesis. -/
@[stacks 0D6W]
theorem homologyMap_isIso_of_pullbackBasis
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisf : PullbackBasis.{w, max z vY, uX, vX, uY, vY, wι} f A)
    (N : ℤ)
    (h_vanish :
      f.modulePushforward.{max z vX vY}.HasCohomologicalDimensionLEOn A N)
    (K : DerivedCategory.CohomologyIn A)
    (n : ℕ) (j : ℤ) (hj : N - (n : ℤ) ≤ j) :
    IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{max z vX vY} Y) j).map
        (lowerStageMap f K.obj n)) := sorry

end PullbackBasis

end RingedSite.Hom.modulePushforwardDerived

end
