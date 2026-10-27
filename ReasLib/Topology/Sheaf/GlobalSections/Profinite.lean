/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Separation.DisjointCover
public import ReasLib.CategoryTheory.Adjunction.Abelian
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Exactness
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import ReasLib.Topology.Sheaves.Glue
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global sections on profinite spaces

Compact Hausdorff totally disconnected spaces admit finite pairwise disjoint clopen refinements.
Consequently, global sections of abelian sheaves preserve epimorphisms and form an exact functor.
The hypotheses are stated as topological typeclasses so the API applies without rebundling a
`TopCat` as `Profinite`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.GlobalSections.Profinite

variable {X : TopCat.{u}} [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

/-- An epimorphism of abelian sheaves on a compact Hausdorff totally disconnected space is
surjective on global sections. -/
@[stacks 0A3F "epimorphisms are surjective on profinite global sections"]
theorem map_surjective {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) [Epi f] :
    Function.Surjective (f.hom.app (op (⊤ : Opens X))) := sorry

/-- Global sections on a compact Hausdorff totally disconnected space preserve epimorphisms. -/
@[stacks 0A3F "profinite global sections preserve epimorphisms"]
instance preservesEpimorphisms (X : TopCat.{u}) [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    (siteAbelianSectionsFunctor
      (Opens.grothendieckTopology X) (⊤ : Opens X)).PreservesEpimorphisms := sorry

/-- Global sections of abelian sheaves on a compact Hausdorff totally disconnected space form an
exact functor. -/
@[stacks 0A3F "exact global sections on profinite spaces"]
theorem exactSections (X : TopCat.{u}) [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    exactFunctor _ _
      (siteAbelianSectionsFunctor
        (Opens.grothendieckTopology X) (⊤ : Opens X)) := sorry

/-- Evaluation on the top open of a compact Hausdorff totally disconnected space preserves
finite colimits.  Together with the existing finite-limit instance, this makes exactness and
homology preservation available to typeclass search. -/
@[stacks 0A3F "profinite top-open sections preserve finite colimits"]
instance sectionsPreservesFiniteColimits (X : TopCat.{u}) [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    PreservesFiniteColimits
      (siteAbelianSectionsFunctor
        (Opens.grothendieckTopology X) (⊤ : Opens X)) := sorry

/-- The canonical global-sections functor on a compact Hausdorff totally disconnected space
preserves epimorphisms.  This is the transport of `preservesEpimorphisms` along
`CategoryTheory.Sheaf.ΓNatIsoSheafSections`. -/
@[stacks 0A3F "canonical profinite global sections preserve epimorphisms"]
instance gammaPreservesEpimorphisms (X : TopCat.{u}) [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    (CategoryTheory.Sheaf.Γ
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesEpimorphisms := sorry

/-- The canonical global-sections functor on a compact Hausdorff totally disconnected space
preserves finite colimits.  The comparison with evaluation on the top open is
`CategoryTheory.Sheaf.ΓNatIsoSheafSections`. -/
@[stacks 0A3F "canonical profinite global sections preserve finite colimits"]
instance gammaPreservesFiniteColimits (X : TopCat.{u}) [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    PreservesFiniteColimits
      (CategoryTheory.Sheaf.Γ
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := sorry

/-- The canonical global-sections functor for abelian sheaves on a compact Hausdorff totally
disconnected space is exact. -/
@[stacks 0A3F "exact canonical global sections on profinite spaces"]
theorem exactGlobalSections (X : TopCat.{u}) [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    exactFunctor _ _
      (CategoryTheory.Sheaf.Γ
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := sorry

end TopCat.Sheaf.GlobalSections.Profinite
