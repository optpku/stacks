/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sets.BaseChangeNhds
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Category.TopCat.Subset
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaf cohomology near a compact subset

This leaf uses Mathlib's bundled compact subsets and their filtered category of open
neighbourhoods.  It owns the canonical comparison from the colimit of neighbourhood cohomology
to the cohomology of the restricted sheaf on the compact subspace.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits
open scoped Topology

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology.CompactSubset

variable {X : TopCat.{u}}

/-- The cohomology diagram `U ↦ H^p(U, F)` on the opposite of the ordered open neighbourhoods of
a compact subset. -/
@[stacks 09V3 "cohomology diagram on compact-subset neighbourhoods"]
abbrev diagram (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    K.openNhdsᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (OrderHom.Subtype.val K.openNhds).toFunctor.op ⋙ F.cohomologyPresheaf p

/-- Cohomology of the restriction of `F` to the subspace carried by a compact subset. -/
@[stacks 09V3 "cohomology target on a compact subspace"]
abbrev subspaceCohomology (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    AddCommGrpCat.{u} :=
  ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
    (TopCat.subsetInclusion (K : Set X))).obj F).H' p
      (⊤ : Opens (TopCat.subsetSpace (K : Set X)))

/-- The inverse image of an open neighbourhood of `K` under the subset inclusion `K ⟶ X` is the
top open of the compact subspace. -/
@[stacks 09V3 "compact-subset inverse image of an open neighbourhood"]
theorem preimageTop (K : Compacts X) (U : K.openNhds) :
    (Opens.map (TopCat.subsetInclusion (K : Set X))).obj U.val =
      (⊤ : Opens (TopCat.subsetSpace (K : Set X))) := sorry

/-- Transport cohomology on the inverse image of a neighbourhood to cohomology on the top open
of the compact subspace. -/
@[stacks 09V3 "compact-subset neighbourhood cohomology transport"]
noncomputable def preimageTopIso (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) (U : K.openNhds) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.subsetInclusion (K : Set X))).obj F).H' p
        ((Opens.map (TopCat.subsetInclusion (K : Set X))).obj U.val) ≅
      subspaceCohomology K F p :=
  eqToIso (congrArg
    (fun V ↦ ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.subsetInclusion (K : Set X))).obj F).H' p V)
    (Opens.ext (Set.eq_univ_of_forall (fun x ↦ U.property x.property))))

/-- The canonical restriction map from cohomology on an open neighbourhood to cohomology of the
restricted sheaf on the compact subspace. -/
@[stacks 09V3 "compact-subset neighbourhood cohomology map"]
noncomputable def stageMap (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) (U : K.openNhds) :
    (diagram K F p).obj (Opposite.op U) ⟶ subspaceCohomology K F p :=
  CategoryTheory.Sheaf.pullbackCohomologyMap
      (TopCat.subsetInclusion (K : Set X)) F p U.val ≫
    (preimageTopIso K F p U).hom

/-- Neighbourhood restriction maps commute with the canonical maps to compact-subspace
cohomology. -/
@[stacks 09V3 "naturality of compact-subset neighbourhood cohomology maps"]
theorem stageMap_naturality (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) {U V : K.openNhdsᵒᵖ} (f : U ⟶ V) :
    (diagram K F p).map f ≫ stageMap K F p V.unop =
      stageMap K F p U.unop := sorry

/-- The canonical cocone from cohomology on open neighbourhoods to cohomology on the compact
subspace. -/
@[stacks 09V3 "compact-subset neighbourhood cohomology cocone"]
noncomputable def cocone (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    Cocone (diagram K F p) where
  pt := subspaceCohomology K F p
  ι :=
    { app U := stageMap K F p U.unop
      naturality _ _ f := stageMap_naturality K F p f }

/-- The canonical map from the colimit of neighbourhood cohomology to cohomology of the compact
subspace. -/
@[stacks 09V3 "compact-subset neighbourhood cohomology comparison"]
noncomputable def comparison (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    colimit (diagram K F p) ⟶ subspaceCohomology K F p :=
  colimit.desc (diagram K F p) (cocone K F p)

/-- The compact-subset comparison restricts at every open neighbourhood to the canonical
pullback map on cohomology. -/
@[reassoc, stacks 09V3 "compact-subset comparison on an open neighbourhood"]
theorem ι_comp_comparison (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) (U : K.openNhdsᵒᵖ) :
    colimit.ι (diagram K F p) U ≫ comparison K F p =
      stageMap K F p U.unop := sorry

/-- Lemma 20.16.3 (09V3): if points of a compact subset have pairwise disjoint ambient
neighbourhood filters, the canonical map from neighbourhood cohomology to cohomology on the
subspace is an isomorphism. -/
@[stacks 09V3 "cohomology of an ambiently separated compact subset"]
theorem comparison_isIso (K : Compacts X)
    (hK : (K : Set X).PairwiseDisjoint (fun x : X ↦ 𝓝 x))
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (comparison K F p) := sorry

end TopCat.Sheaf.Cohomology.CompactSubset
