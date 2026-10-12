/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of sites

A morphism of sites `(D, K) → (C, J)` is a functor `u : C ⥤ D` (note: the functor
goes in the OPPOSITE direction to the morphism of sites) that is both continuous
and representably flat.

## Convention boundary

This file uses the representably-flat convention of SGA 4 and the Stacks Project.  Some broader
sources, including nLab, use the weaker pair "covering-flat and cover-preserving" as their basic
definition.  ReasLib does not identify those notions without the hypotheses under which they
agree.  At the present level, Mathlib's `Functor.isContinuous_iff_coverPreserving` gives the
precise bridge: for a representably flat functor, continuity is equivalent to preserving covering
sieves.

## Direction convention

The functor `u : C ⥤ D` induces a morphism of SITES in the direction `(D, K) → (C, J)`,
and a morphism of TOPOI in the direction `Sh(K) → Sh(J)`. The inverse image
`u* : Sh(K) → Sh(J)` goes in the same direction as the site morphism, while
`u` itself goes the other way. This is standard (SGA 4, Expose III).

## Main results

- `IsMorphismOfSites` — the class bundling continuity + representable flatness
- `IsMorphismOfSites.toMorphismOfTopoiIn` — every site morphism induces a topos morphism
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A morphism of sites `(D, K) → (C, J)` is a functor `u : C ⥤ D` that is both continuous
(precomposition preserves sheaves) and representably flat (the induced inverse image on sheaves
is left exact).  Under representable flatness, continuity is equivalently preservation of
covering sieves; this is the common stronger morphism-of-sites convention, not the most general
covering-flat convention.

Note: the functor goes C → D but the induced site morphism goes (D,K) → (C,J). -/
@[stacks 04WJ "morphism-of-sites hypothesis for inverse-image stacks"]
class IsMorphismOfSites
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) : Prop
    extends u.IsContinuous J K, RepresentablyFlat u

attribute [stacks 04WJ "site-morphism continuity field"]
  IsMorphismOfSites.toIsContinuous
attribute [stacks 04WJ "site-morphism representable-flatness field"]
  IsMorphismOfSites.toRepresentablyFlat

/-- A functor is a morphism of sites iff it is continuous and representably flat. -/
@[simp, stacks 04WJ "morphism-of-sites defining conditions"]
theorem isMorphismOfSites_iff
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D) :
    IsMorphismOfSites J K u ↔ u.IsContinuous J K ∧ RepresentablyFlat u := sorry

/-- The ReasLib morphism-of-sites condition is equivalently preservation of covering sieves
together with representable flatness.  This is the direct bridge to the common cover-preserving
formulation, while keeping the weaker covering-flat convention outside this owner. -/
@[stacks 04WJ "cover-preserving characterization of a morphism of sites"]
theorem IsMorphismOfSites.iff_coverPreserving
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) :
    IsMorphismOfSites J K u ↔ CoverPreserving J K u ∧ RepresentablyFlat u := sorry

/-- A site morphism exposes the cover-preserving half of its Mathlib characterization. -/
@[stacks 04WJ "cover-preserving readout of a morphism of sites"]
theorem IsMorphismOfSites.coverPreserving
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
    [IsMorphismOfSites J K u] :
    CoverPreserving J K u := sorry

/-- Construct the ReasLib site-morphism condition from cover preservation and representable
flatness.  The flatness assumption remains a typeclass input because it supplies the canonical
left-exactness infrastructure used by Mathlib. -/
@[stacks 04WJ "construct a morphism of sites from cover preservation"]
theorem IsMorphismOfSites.of_coverPreserving
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
    [RepresentablyFlat u] (h : CoverPreserving J K u) :
    IsMorphismOfSites J K u := sorry

/-- Constructor: a continuous representably flat functor is a morphism of sites. -/
@[stacks 04WJ "construct a morphism of sites from continuity and flatness"]
instance IsMorphismOfSites.mk'
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [u.IsContinuous J K] [RepresentablyFlat u] :
    IsMorphismOfSites J K u where

/-- The identity functor is a morphism of sites. -/
@[stacks 04WJ "identity morphism of sites"]
instance IsMorphismOfSites.id (J : GrothendieckTopology C) :
    IsMorphismOfSites J J (𝟭 C) := sorry

/-- Composition of morphisms of sites with an explicitly supplied middle topology. The middle
topology cannot be recovered from the composite alone, so this is a theorem rather than a global
typeclass instance. -/
@[stacks 04WJ "composition of morphisms of sites"]
theorem IsMorphismOfSites.comp {E : Type*} [Category E]
    {J : GrothendieckTopology C} (K : GrothendieckTopology D) {L : GrothendieckTopology E}
    (u : C ⥤ D) (v : D ⥤ E) [IsMorphismOfSites J K u] [IsMorphismOfSites K L v] :
    IsMorphismOfSites J L (u ⋙ v) := sorry

/-- The key theorem: a morphism of sites induces a morphism of topoi `Sh(K) → Sh(J)`.
The inverse image is the sheaf pullback `u.sheafPullback`, which is left-exact
because `u` is representably flat. -/
noncomputable def IsMorphismOfSites.toMorphismOfTopoiIn
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : C ⥤ D) [IsMorphismOfSites J K u]
    [HasWeakSheafify K (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits (u.sheafPullback (Type w) J K)] :
    MorphismOfTopoiIn J K :=
  u.morphismOfTopoiInOfContinuous J K

attribute [stacks 04WJ "site-morphism topos morphism bridge"]
  IsMorphismOfSites.toMorphismOfTopoiIn


end CategoryTheory
