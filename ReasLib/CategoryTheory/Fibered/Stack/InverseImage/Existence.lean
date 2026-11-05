/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Local
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Existence
public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence and comparison of inverse-image stacks

This leaf separates the existence theorem, which needs smallness and stackification machinery,
from the lightweight `StackOver.InverseImage` data owner.  Inverse-image stacks are noncanonical,
so the public API keeps a chosen value explicit and records independence by an equivalence between
any two choices.
-/

@[expose] public section

universe wD uC uD vC vD uS vS uT1 vT1 uT2 vT2

namespace CategoryTheory

open Limits
open scoped Bicategory

namespace StackOver.InverseImage

section Existence

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Form the inverse image by the concrete stackification of the certified localized
pushforward. The target and comparison are supplied by the local-descent construction,
rather than selected from a stackification existence theorem. -/
noncomputable def ofProjection
    (u : C ⥤ D)
    {S : StackOver.{uC, vC, uS, vS} J}
    (hS : FiberedCategoryOver.Pushforward.ProjectionChoice u S.toFiberedCategoryOver) :
    StackOver.InverseImage K u S where
  sourceChoice := hS
  target := Functor.StackificationConstruction.canonicalTarget K
    (StackOver.inverseImageSource u S hS).p
  comparison := Functor.StackificationConstruction.canonicalComparison K
    (StackOver.inverseImageSource u S hS).p
  isStackification := Functor.StackificationConstruction.canonicalIsStackification K
    (StackOver.inverseImageSource u S hS).p

/-- Definition 8.12.9 (tag 04WJ), existence: an inverse-image stack exists once a fibred
pushforward projection is fixed. The source stack may live in arbitrary total-category
universes; only the newly constructed target is placed in the common universe bound required by
the localization and stackification constructions. The result is kept in `Nonempty` because
neither the target stackification nor its comparison is canonical. -/
@[stacks 04WJ "existence of inverse-image stacks"]
theorem nonempty
    (u : C ⥤ D) [Small.{wD} D]
    {S : StackOver.{uC, vC, uS, vS} J}
    (hS : FiberedCategoryOver.Pushforward.ProjectionChoice u S.toFiberedCategoryOver) :
    Nonempty (StackOver.InverseImage.{
      uC, uD, vC, vD, uS, vS,
      max uC (max uD (max uS (max vC (max vD vS)))),
      max uC (max uD (max uS (max vC (max vD vS))))} K u S) :=
  ⟨ofProjection u hS⟩

/-- Definition 8.12.9 (tag 04WJ), canonical existence: under the finite-limit hypotheses used
to construct the fibred pushforward, an inverse-image stack exists without requiring callers to
thread a projection choice. Consumers that must pin a particular localization presentation can
use `nonempty` instead. -/
@[stacks 04WJ "canonical existence of inverse-image stacks"]
theorem nonemptyCanonical
    (u : C ⥤ D) [Small.{wD} D]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S : StackOver.{uC, vC, uS, vS} J} :
    Nonempty (StackOver.InverseImage.{
      uC, uD, vC, vD, uS, vS,
      max uC (max uD (max uS (max vC (max vD vS)))),
      max uC (max uD (max uS (max vC (max vD vS))))} K u S) :=
  nonempty u (FiberedCategoryOver.Pushforward.ProjectionChoice.canonical u
    S.toFiberedCategoryOver)

/-!
The existence theorems above remain proposition-valued. The following convenience value uses
the same concrete stackification as `ofProjection`, with the standard pushforward certification.
It does not eliminate an admitted inverse-image existence theorem to obtain its data.
-/

/-- The inverse-image stack formed by concrete stackification of the finite-limit pushforward.
Use `ofProjection` to supply a particular pushforward certification. -/
@[stacks 04WJ "canonical inverse-image stack choice"]
noncomputable def canonical
    (u : C ⥤ D) [Small.{wD} D]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S : StackOver.{uC, vC, uS, vS} J} :
    StackOver.InverseImage K u S :=
  ofProjection u (FiberedCategoryOver.Pushforward.ProjectionChoice.canonical u
    S.toFiberedCategoryOver)

/-- The canonical choice satisfies the defining stackification specification of an inverse-image
stack.  Downstream code should use this named readout instead of unfolding `canonical`. -/
@[stacks 04WJ "canonical inverse-image stack specification"]
theorem canonical_spec
    (u : C ⥤ D) [Small.{wD} D]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S : StackOver.{uC, vC, uS, vS} J} :
    CartesianBasedFunctor.IsStackification K
      (canonical (K := K) (S := S) u).comparison :=
  (canonical (K := K) (S := S) u).isStackification

end Existence

section Comparison

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Definition 8.12.9 (tag 04WJ), uniqueness: any two inverse-image stacks of the same source
admit a heterogeneous cartesian equivalence compatible with their stackification comparisons,
and every other compatible comparison is uniquely `2`-isomorphic to it. The two target total
categories may live in independent universes. -/
@[stacks 04WJ "uniqueness of inverse-image stack comparisons"]
theorem comparisonUnique
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    (I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S)
    (I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S) :
    ∃ e : CartesianBasedFunctor I.target.p I'.target.p,
      e.toBasedFunctor.IsEquivalence ∧
        ∃ α : (CartesianBasedFunctor.precomp I'.target.p I.comparison).obj e ≅ I'.comparison,
          ∀ (H : CartesianBasedFunctor I.target.p I'.target.p)
              (α' : (CartesianBasedFunctor.precomp I'.target.p I.comparison).obj H ≅
                I'.comparison),
            ∃! β : e ≅ H,
              (CartesianBasedFunctor.precomp I'.target.p I.comparison).mapIso β ≪≫ α' = α := sorry

/-- Definition 8.12.9 (tag 04WJ), comparison: any two inverse-image stacks of the same source are
heterogeneously equivalent compatibly with their stackification comparisons. This is the
lightweight existence corollary of `comparisonUnique` for consumers that do not need uniqueness
of the compatible `2`-isomorphism. -/
@[stacks 04WJ "comparison equivalence between inverse-image stacks"]
theorem existsComparisonEquivalence
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    (I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S)
    (I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S) :
    ∃ e : CartesianBasedFunctor I.target.p I'.target.p,
      e.toBasedFunctor.IsEquivalence ∧
        Nonempty
            ((CartesianBasedFunctor.precomp I'.target.p I.comparison).obj e ≅
            I'.comparison) :=
  CartesianBasedFunctor.IsStackification.existsComparisonEquivalence
    I.comparison I'.comparison I.isStackification I'.isStackification

/-- Explicit comparison data between two inverse-image stack presentations.

The target equivalence and its structure isomorphism are concrete data.  The stackification
proofs remain fields of the two `InverseImage` objects and are not duplicated here.  This is the
heterogeneous owner: fixed bundled consumers can use the thin comparison corollary below without
making the universe-polymorphic data depend on a common total-category universe. -/
@[stacks 04WJ "explicit inverse-image comparison data"]
structure ComparisonChoice
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    (I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S)
    (I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S) where
  /-- The cartesian equivalence between the two inverse-image targets. -/
  comparison : CartesianBasedFunctor I.target.p I'.target.p
  /-- The underlying based functor of the comparison is an equivalence. -/
  isEquivalence : comparison.toBasedFunctor.IsEquivalence
  /-- The comparison isomorphism over the common pushforward source. -/
  iso : (CartesianBasedFunctor.precomp I'.target.p I.comparison).obj comparison ≅
    I'.comparison

attribute [stacks 04WJ "inverse-image comparison functor"] ComparisonChoice.comparison
attribute [stacks 04WJ "inverse-image comparison equivalence"] ComparisonChoice.isEquivalence
attribute [stacks 04WJ "inverse-image comparison structure isomorphism"] ComparisonChoice.iso

/-- Package explicitly supplied inverse-image comparison data.

This deterministic constructor is preferred when the consumer already owns the target
equivalence and its comparison isomorphism. -/
@[stacks 04WJ "package explicit inverse-image comparison data"]
def ComparisonChoice.of
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    {I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S}
    {I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S}
    (e : CartesianBasedFunctor I.target.p I'.target.p)
    (he : e.toBasedFunctor.IsEquivalence)
    (α : (CartesianBasedFunctor.precomp I'.target.p I.comparison).obj e ≅
      I'.comparison) :
    ComparisonChoice I I' :=
  ⟨e, he, α⟩

/-- Convert an existential comparison theorem into the named inverse-image data owner.

This is the only proposition-to-data boundary for the comparison itself.  Callers with explicit
data should use `ComparisonChoice.of` instead of selecting a witness from an existential. -/
@[stacks 04WJ "package an existential inverse-image comparison"]
noncomputable def ComparisonChoice.ofExists
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    {I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S}
    {I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S}
    (h : ∃ e : CartesianBasedFunctor I.target.p I'.target.p,
      e.toBasedFunctor.IsEquivalence ∧
        Nonempty
          ((CartesianBasedFunctor.precomp I'.target.p I.comparison).obj e ≅
            I'.comparison)) :
    ComparisonChoice I I' where
  comparison := Classical.choose h
  isEquivalence := (Classical.choose_spec h).1
  iso := Classical.choice (Classical.choose_spec h).2

/-- Two inverse-image presentations have a nonempty type of explicit comparison data. -/
@[stacks 04WJ "existence of explicit inverse-image comparison data"]
theorem ComparisonChoice.nonempty
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    {I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S}
    {I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S} :
    Nonempty (ComparisonChoice I I') := by
  let A := CartesianBasedFunctor.IsStackification.comparisonChoice
    I.isStackification I'.isStackification
  exact ⟨⟨A.comparison, A.isEquivalence, A.iso⟩⟩

/-- Form an inverse-image comparison from the explicit stackification comparison.

The functor and structure isomorphism are the actual universal-property lift data. In particular,
the admitted equivalence proof is only a Prop field, never part of a proposition from which these
data are selected. Downstream code should use the fields and the uniqueness API below. -/
@[stacks 04WJ "selected inverse-image comparison"]
noncomputable def comparisonChoice
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    (I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S)
    (I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S) :
    ComparisonChoice I I' :=
  let A := CartesianBasedFunctor.IsStackification.comparisonChoice
    I.isStackification I'.isStackification
  ⟨A.comparison, A.isEquivalence, A.iso⟩

/-- Any two explicit inverse-image comparisons admit a unique compatible comparison isomorphism. -/
@[stacks 04WJ "existence and uniqueness of inverse-image comparison isomorphisms"]
theorem ComparisonChoice.existsUniqueIso
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    {I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S}
    {I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S}
    (A B : ComparisonChoice I I') :
    ∃! β : A.comparison ≅ B.comparison,
      (CartesianBasedFunctor.precomp I'.target.p I.comparison).mapIso β ≪≫ B.iso = A.iso :=
  CartesianBasedFunctor.IsStackification.LiftChoice.existsUniqueComparisonIso
    I.isStackification ⟨A.comparison, A.iso⟩ ⟨B.comparison, B.iso⟩

/-- The compatible isomorphism between two explicit inverse-image comparisons, formed by
gluing their local components through the stackification universal property. This reuses the
explicit descent construction rather than selecting data from `existsUniqueIso`. -/
@[stacks 04WJ "selected inverse-image comparison isomorphism"]
noncomputable def ComparisonChoice.comparisonIso
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    {I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S}
    {I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S}
    (A B : ComparisonChoice I I') : A.comparison ≅ B.comparison :=
  CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso
    I.isStackification ⟨A.comparison, A.iso⟩ ⟨B.comparison, B.iso⟩

/-- The selected inverse-image comparison isomorphism has the expected compatibility equation. -/
@[stacks 04WJ "specification of selected inverse-image comparison isomorphism"]
theorem ComparisonChoice.comparisonIso_spec
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    {I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S}
    {I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S}
    (A B : ComparisonChoice I I') :
    (CartesianBasedFunctor.precomp I'.target.p I.comparison).mapIso
        (ComparisonChoice.comparisonIso A B) ≪≫ B.iso = A.iso :=
  CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso_spec
    I.isStackification ⟨A.comparison, A.iso⟩ ⟨B.comparison, B.iso⟩

/-- Any compatible inverse-image comparison isomorphism equals the selected one. -/
@[stacks 04WJ "uniqueness of selected inverse-image comparison isomorphism"]
theorem ComparisonChoice.comparisonIso_unique
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    {I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S}
    {I' : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT2, vT2} K u S}
    (A B : ComparisonChoice I I')
    (β : A.comparison ≅ B.comparison)
    (hβ : (CartesianBasedFunctor.precomp I'.target.p I.comparison).mapIso β ≪≫ B.iso = A.iso) :
    β = ComparisonChoice.comparisonIso A B :=
  CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso_unique
    I.isStackification ⟨A.comparison, A.iso⟩ ⟨B.comparison, B.iso⟩ β hβ

namespace canonical

/-- Any explicit inverse-image presentation is comparable with the canonical choice by the
heterogeneous equivalence compatible with both stackification comparisons.  This is the
choice-independence bridge for downstream constructions. -/
@[stacks 04WJ "canonical inverse-image choice comparison"]
theorem comparison
    (u : C ⥤ D) [Small.{wD} D]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S : StackOver.{uC, vC, uS, vS} J}
    (I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S) :
    ∃ e : CartesianBasedFunctor (canonical (K := K) (S := S) u).target.p I.target.p,
      e.toBasedFunctor.IsEquivalence ∧
        Nonempty
          ((CartesianBasedFunctor.precomp I.target.p
            (canonical (K := K) (S := S) u).comparison).obj e ≅
            I.comparison) :=
  existsComparisonEquivalence (canonical (K := K) (S := S) u) I

/-- Package the canonical inverse-image comparison with an explicit presentation into the shared
`ComparisonChoice` owner.  The source-facing existential `canonical.comparison` remains available
for consumers that only need existence. -/
@[stacks 04WJ "canonical inverse-image comparison choice"]
noncomputable def comparisonChoice
    (u : C ⥤ D) [Small.{wD} D]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    {S : StackOver.{uC, vC, uS, vS} J}
    (I : StackOver.InverseImage.{uC, uD, vC, vD, uS, vS, uT1, vT1} K u S) :
    ComparisonChoice (canonical (K := K) (S := S) u) I :=
  ComparisonChoice.ofExists (comparison u I)

end canonical

/-- Fixed-universe specialization of `comparisonUnique` for consumers already working in the
bundled stack bicategory. -/
@[stacks 04WJ "fixed-universe uniqueness of inverse-image comparisons"]
theorem comparisonHomUnique
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    (I I' : StackOver.InverseImage K u S) :
    ∃ e : I.target ≌ I'.target,
      ∃ α : (StackOver.Hom.precomp I'.target I.comparisonHom).obj e.hom ≅ I'.comparisonHom,
        ∀ (H : I.target ⟶ I'.target)
            (α' : (StackOver.Hom.precomp I'.target I.comparisonHom).obj H ≅ I'.comparisonHom),
          ∃! β : e.hom ≅ H,
            (StackOver.Hom.precomp I'.target I.comparisonHom).mapIso β ≪≫ α' = α := sorry

/-- Fixed-universe comparison corollary for consumers that only need a compatible equivalence
of bundled stacks. -/
@[stacks 04WJ "fixed-universe comparison equivalence between inverse-image stacks"]
theorem existsComparisonHomEquivalence
    {u : C ⥤ D}
    {S : StackOver.{uC, vC, uS, vS} J}
    (I I' : StackOver.InverseImage K u S) :
    ∃ e : I.target ≌ I'.target,
      Nonempty
        ((StackOver.Hom.precomp I'.target I.comparisonHom).obj e.hom ≅
          I'.comparisonHom) := sorry

end Comparison

/- Data audit: `ofProjection` and `canonical` use the concrete stackification target and
comparison. The standard pushforward fibredness certification still has proof debt; its use by
the construction's chosen cleavage must be audited separately. `ComparisonChoice.ofExists`
and `LiftChoice.ofExists` select data satisfying caller-supplied comparison equations.
`comparisonChoice` and `canonical.comparisonChoice` use the proved comparison existence
projection of the explicit stackification lift; any remaining debt in its descent construction
is inherited rather than a fresh admitted inverse-image comparison existence theorem. -/

end StackOver.InverseImage

end CategoryTheory
