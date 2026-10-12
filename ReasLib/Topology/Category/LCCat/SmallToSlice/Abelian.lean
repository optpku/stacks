/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.LCCat.SmallToSlice
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Sheaf
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Exactness
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction

/-!
# Abelian sheaves on the small-to-slice morphism

This file owns the abelian inverse and direct images attached to the canonical functor
`LCCat.opensOver X`.  Both functors are exact, so their adjunction descends directly to
unbounded derived categories.  The derived unit is the reusable core behind the cohomology
comparisons of Lemma 21.31.7.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty TopologicalSpace
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace LCCat.SmallToSlice

variable (X : LCCat.{u})

section SmallPullback

variable {X Y : LCCat.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]

/-- Inverse image on abelian sheaves between the small open sites of `Y` and `X`. -/
@[stacks 0DCU "small-site inverse image"]
noncomputable abbrev smallPullback :
    Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (Opens.map f.hom) AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology Y.obj) (Opens.grothendieckTopology X.obj)

/-- Small-site inverse image is additive. -/
@[stacks 0DCU "small-site inverse image additive", instance]
noncomputable instance smallPullback_additive : (smallPullback f).Additive := sorry

/-- Small-site inverse image preserves finite limits. -/
@[stacks 0DCU "small-site inverse image finite limits", instance]
noncomputable instance smallPullback_preservesFiniteLimits :
    PreservesFiniteLimits (smallPullback f) := sorry

/-- Small-site inverse image preserves finite colimits. -/
@[stacks 0DCU "small-site inverse image finite colimits", instance]
noncomputable instance smallPullback_preservesFiniteColimits :
    PreservesFiniteColimits (smallPullback f) := sorry

/-- Small-site inverse image, bundled as an exact functor. -/
@[stacks 0DCU "exact small-site inverse image"]
noncomputable abbrev smallPullbackExact :
    Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (smallPullback f)

end SmallPullback

section Underived

variable [HasWeakSheafify (zarTopology.over X) AddCommGrpCat.{u + 1}]

/-- The inverse image on abelian sheaves from the small open site of `X` to the Zariski slice
site.  It is the explicit left-Kan-extension and sheafification construction. -/
@[stacks 0DCU "small-to-slice abelian inverse image"]
noncomputable abbrev abPullback :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1} ⥤
      Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (opensOver X) AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (zarTopology.over X)

/-- The direct image on abelian sheaves from the Zariski slice site to the small open site. -/
@[stacks 0DCU "small-to-slice abelian direct image"]
abbrev abPushforward :
    Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1} :=
  (opensOver X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (zarTopology.over X)

/-- The explicit adjunction between small-to-slice inverse and direct image. -/
@[stacks 0DCU "small-to-slice abelian adjunction"]
noncomputable def abAdjunction : abPullback X ⊣ abPushforward X :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (opensOver X) AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (zarTopology.over X)

section AInverse

variable [HasWeakSheafify (qcTopology.over X) AddCommGrpCat.{u + 1}]

/-- The canonical abelian inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹`. -/
@[stacks 0DCY "canonical abelian inverse image a_X⁻¹"]
noncomputable abbrev aInverseAb :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1} ⥤
      Sheaf (qcTopology.over X) AddCommGrpCat.{u + 1} :=
  abPullback X ⋙ comparisonTopologyPullbackAb zar_le_qc X

end AInverse

/-- The explicit Kan-extension model agrees with mathlib's chosen small-to-slice left adjoint. -/
@[stacks 0DCU "canonical/explicit inverse-image comparison"]
noncomputable def abPullbackIso :
    (opensOver X).sheafPullback AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.obj) (zarTopology.over X) ≅ abPullback X :=
  Functor.sheafPullbackConstruction.sheafPullbackIso
    (opensOver X) AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.obj) (zarTopology.over X)

/-- The source subcategory `A'_X` consisting of objects obtained from the small open site. -/
@[stacks 0EZI "essential image of the small-to-slice inverse image"]
abbrev essImageAb :
    ObjectProperty (Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1}) :=
  Functor.essImage (abPullback X)

/-- Every canonical small-to-slice inverse-image object belongs to `essImageAb X`. -/
@[stacks 0EZI "essential-image membership"]
theorem obj_mem_essImageAb
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) :
    essImageAb X ((abPullback X).obj F) := sorry

/-- Membership in the canonical essential image is detected by the adjunction counit. -/
@[stacks 0EZI "essential image iff counit is invertible"]
theorem mem_essImageAb_iff_counit_isIso
    (F : Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1}) :
    essImageAb X F ↔ IsIso ((abAdjunction X).counit.app F) := sorry

/-- The canonical essential image is weak Serre in the Zariski slice category. -/
@[stacks 0EZI "weak Serre essential image"]
instance essImageAb_isWeakSerre :
    IsWeakSerreClass (essImageAb X) := sorry

/-- Lemma 21.31.7: the canonical small-to-slice inverse image is additive. -/
@[stacks 0DCU "small-to-slice inverse image additive", instance]
instance abPullback_additive : (abPullback X).Additive := sorry

/-- Lemma 21.31.7: the canonical small-to-slice direct image is additive. -/
@[stacks 0DCU "small-to-slice direct image additive", instance]
instance abPushforward_additive : (abPushforward X).Additive := sorry

end Underived

section Exact

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify (zarTopology.over X) AddCommGrpCat.{u + 1}]

/-- Lemma 21.31.7: the canonical small-to-slice inverse image preserves finite limits. -/
@[stacks 0DCU "small-to-slice inverse image finite limits", instance]
instance abPullback_preservesFiniteLimits : PreservesFiniteLimits (abPullback X) := sorry

/-- Lemma 21.31.7: the canonical small-to-slice inverse image preserves finite colimits. -/
@[stacks 0DCU "small-to-slice inverse image finite colimits", instance]
instance abPullback_preservesFiniteColimits : PreservesFiniteColimits (abPullback X) := sorry

/-- Lemma 21.31.7 (2): small-to-slice direct image is exact. -/
@[stacks 0DCU "(2)"]
theorem abPushforward_exact :
    exactFunctor
      (Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1})
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})
      (abPushforward X) := sorry

/-- Lemma 21.31.7: the canonical small-to-slice direct image preserves finite limits. -/
@[stacks 0DCU "small-to-slice direct image finite limits", instance]
instance abPushforward_preservesFiniteLimits : PreservesFiniteLimits (abPushforward X) := sorry

/-- Lemma 21.31.7: the canonical small-to-slice direct image preserves finite colimits. -/
@[stacks 0DCU "small-to-slice direct image finite colimits", instance]
instance abPushforward_preservesFiniteColimits : PreservesFiniteColimits (abPushforward X) := sorry

/-- Lemma 21.31.7 (3): the unit of the small-to-slice adjunction is invertible. -/
@[stacks 0DCU "(3)", instance]
theorem abUnit_isIso : IsIso (abAdjunction X).unit := sorry

/-- Every component of the small-to-slice unit is invertible. -/
@[stacks 0DCU "(3), component of the small-to-slice unit", instance]
instance abUnit_app_isIso
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) :
    IsIso ((abAdjunction X).unit.app F) := sorry

end Exact

section Derived

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify (zarTopology.over X) AddCommGrpCat.{u + 1}]

/-- The exact inverse image on unbounded derived categories. -/
@[stacks 0DCU "unbounded small-to-slice inverse image"]
noncomputable abbrev derivedPullback :
    DerivedCategory
        (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1}) :=
  (abPullback X).mapDerivedCategory

/-- The exact direct image on unbounded derived categories. -/
@[stacks 0DCU "unbounded small-to-slice direct image"]
noncomputable abbrev derivedPushforward :
    DerivedCategory (Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory
        (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) :=
  (abPushforward X).mapDerivedCategory

/-- The small-to-slice adjunction on unbounded derived categories. -/
@[stacks 0DCU "unbounded small-to-slice adjunction"]
noncomputable def derivedAdjunction : derivedPullback X ⊣ derivedPushforward X :=
  CategoryTheory.Adjunction.mapDerivedCategory (abAdjunction X)

/-- The canonical unit from a small-site complex to its pullback followed by derived direct
image. -/
@[stacks 0DCU "canonical unbounded derived unit"]
noncomputable abbrev derivedUnit :
    𝟭
          (DerivedCategory
          (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})) ⟶
      derivedPullback X ⋙ derivedPushforward X :=
  (derivedAdjunction X).unit

/-- The small-to-slice inverse image on bounded-below derived categories. -/
@[stacks 0DCU "bounded-below small-to-slice inverse image"]
noncomputable abbrev abPullbackPlus :
    DerivedCategory.Plus
        (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (ExactFunctor.of (abPullback X))

/-- Lemma 21.31.7 (4): the canonical unbounded derived unit is invertible. -/
@[stacks 0DCU "(4)", instance]
theorem derivedUnit_isIso : IsIso (derivedUnit X) := sorry

/-- Objectwise form of the invertibility of the canonical unbounded derived unit. -/
@[stacks 0DCU "(4), component of the canonical derived unit", instance]
instance derivedUnit_app_isIso
    (K : DerivedCategory
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})) :
    IsIso ((derivedUnit X).app K) := sorry

section Cohomology

variable [HasExt.{u + 1}
  (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1})]

/-- Objectwise cohomology on the small open site, with the coefficient universe fixed at the
source-compatible level `u + 1`. -/
@[stacks 0DCU "small-site objectwise cohomology"]
noncomputable abbrev smallCohomology
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})
    (U : Opens X.obj) (n : ℕ) : AddCommGrpCat.{u + 1} :=
  @CategoryTheory.Sheaf.cohomologyOverObject.{u + 1, u + 1, u, u}
    (Opens X.obj) _ (Opens.grothendieckTopology X.obj) F inferInstance inferInstance U n

/-- Objectwise cohomology on the Zariski slice of `X`, with the coefficient universe fixed at the
source-compatible level `u + 1`. -/
@[stacks 0DCU "slice objectwise cohomology"]
noncomputable abbrev sliceCohomology
    (F : Sheaf (zarTopology.over X) AddCommGrpCat.{u + 1})
    (U : Over X) (n : ℕ) : AddCommGrpCat.{u + 1} :=
  @CategoryTheory.Sheaf.cohomologyOverObject.{u + 1, u + 1, u, u + 1}
    (Over X) _ (zarTopology.over X) F inferInstance inferInstance U n

/-- Lemma 21.31.7 (1): cohomology on the Zariski slice of `X` after small-to-slice inverse
image agrees with cohomology on the small open site of `X`.  The reusable canonical map is the
derived unit `derivedUnit X`; this is its source-facing objectwise cohomology view. -/
@[stacks 0DCU "(1)"]
theorem cohomology_isomorphic
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsIsomorphic
      (sliceCohomology X ((abPullback X).obj F) (Over.mk (𝟙 X)) n)
      (smallCohomology X F (⊤ : Opens X.obj) n) := sorry

end Cohomology

end Derived

section RelativeHypercohomology

variable {X Y : LCCat.{u}} (f : X ⟶ Y)
variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{u + 1}]
variable [HasSheafify (zarTopology.over Y) AddCommGrpCat.{u + 1}]
variable [IsGrothendieckAbelian
  (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian
  (Sheaf (zarTopology.over Y) AddCommGrpCat.{u + 1})]

/-- The inverse image between small open sites on bounded-below derived categories. -/
@[stacks 0DCU "bounded-below small-site inverse image"]
noncomputable abbrev smallPullbackPlus :
    DerivedCategory.Plus
        (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus
        (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u + 1}) :=
  ExactFunctor.Derived.Plus.functor (smallPullbackExact f)

/-- The bounded-below derived sections of `π_Y⁻¹L` over the slice object `f` agree with the
derived sections of `f⁻¹L` on `X`.  This is the reusable all-degree core of Lemma 21.31.7 (6). -/
@[stacks 0DCU "(6), derived sections"]
theorem derivedSections_isomorphic
    (L : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((siteAbelianSectionsBoundedBelowDerived (zarTopology.over Y) (Over.mk f)).obj
        ((abPullbackPlus Y).obj L))
      ((siteAbelianSectionsBoundedBelowDerived
        (Opens.grothendieckTopology X.obj) (⊤ : Opens X.obj)).obj
        ((smallPullbackPlus f).obj L)) := sorry

/-- Lemma 21.31.7 (6): for `f : X ⟶ Y` and a bounded-below complex `L` on the small
open site of `Y`, cohomology of `π_Y⁻¹L` over the slice object `f` agrees with cohomology of
`f⁻¹L` on `X`. -/
@[stacks 0DCU "(6)"]
theorem hypercohomology_isomorphic
    (L : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    IsIsomorphic
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsBoundedBelowDerived (zarTopology.over Y) (Over.mk f)).obj
          ((abPullbackPlus Y).obj L)))
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsBoundedBelowDerived
          (Opens.grothendieckTopology X.obj) (⊤ : Opens X.obj)).obj
          ((smallPullbackPlus f).obj L))) := sorry

end RelativeHypercohomology

/- `aInverseAb` is the explicit composite of the two canonical inverse-image functors; its
reported `sorryAx` is inherited from their Prop-valued continuity and sheafification owners. -/

end LCCat.SmallToSlice

end
