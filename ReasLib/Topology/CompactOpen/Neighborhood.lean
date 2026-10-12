/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Topology.NhdsKer
public import Mathlib.Topology.Sets.BaseChangeNhds
public import Mathlib.Topology.Spectral.Prespectral
public import ReasLib.Topology.CompactOpen.Intersection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compact-open neighbourhoods of compact subsets

This file refines Mathlib's ordered type `K.openNhds` of all open neighbourhoods to the
compact-open neighbourhoods available in a prespectral space.  The inclusion is initial, so its
opposite is final and may be used directly to reindex filtered colimits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

noncomputable section

universe u v w

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace.Compacts

/-- The compact-open subsets containing a compact subset `K`. -/
@[stacks 0A3D "compact-open neighbourhoods of a compact subset"]
def compactOpenNhds (K : Compacts X) : Set (CompactOpens X) :=
  {U | (K : Set X) ⊆ U}

namespace CompactOpenNhds

variable (K : Compacts X)

/-- A compact subset of a prespectral space has a compact-open neighbourhood. -/
noncomputable instance [PrespectralSpace X] : Nonempty K.compactOpenNhds := sorry

/-- Compact-open neighbourhoods are downward directed when compact opens are closed under
intersection. -/
instance [QuasiSeparatedSpace X] : IsCodirectedOrder K.compactOpenNhds := sorry

/-- When the ambient space is compact, its top compact open is the largest compact-open
neighbourhood of `K`. -/
instance [CompactSpace X] : Top K.compactOpenNhds :=
  ⟨⟨⊤, Set.subset_univ _⟩⟩

/-- Forgetting compactness sends compact-open neighbourhoods to open neighbourhoods
monotonically. -/
theorem toOpenNhdsMonotone :
    Monotone (fun U : K.compactOpenNhds ↦
      (⟨U.1.toOpens, U.2⟩ : K.openNhds)) := sorry

/-- The ordered inclusion of compact-open neighbourhoods into all open neighbourhoods. -/
@[stacks 0A3D "compact-open to open neighbourhood inclusion"]
def toOpenNhds : K.compactOpenNhds →o K.openNhds :=
  ⟨fun U ↦ ⟨U.1.toOpens, U.2⟩, toOpenNhdsMonotone K⟩

/-- The compact open underlying `toOpenNhds` is unchanged. -/
@[simp]
theorem toOpenNhds_apply (U : K.compactOpenNhds) :
    (toOpenNhds K U).1 = U.1.toOpens := sorry

/-- Compact-open neighbourhoods are initial among all open neighbourhoods in a prespectral,
quasi-separated space.  Consequently, the opposite functor is final. -/
@[stacks 0A3D "compact-open neighbourhoods are cofinal"]
noncomputable instance toOpenNhdsInitial
    [PrespectralSpace X] [QuasiSeparatedSpace X] :
    Functor.Initial (toOpenNhds K).toFunctor := sorry

/-- The compact-open neighbourhoods present `nhdsKer K` as their directed intersection. -/
@[stacks 0A31 "canonical compact-open neighbourhood intersection",
  stacks 0A3D "specializing subset as compact-open neighbourhood intersection"]
theorem isDirectedIntersection [PrespectralSpace X] [QuasiSeparatedSpace X] :
    IsCompactOpenDirectedIntersection (nhdsKer (K : Set X)) K.compactOpenNhds := sorry

variable {C : Type w} [Category.{v} C]

/-- The canonical comparison from the colimit over compact-open neighbourhoods to the colimit
over all open neighbourhoods. -/
@[stacks 0A3D "compact-open neighbourhood colimit comparison"]
noncomputable def colimitComparison (D : K.openNhdsᵒᵖ ⥤ C) [HasColimit D]
    [HasColimit ((toOpenNhds K).toFunctor.op ⋙ D)] :
    colimit ((toOpenNhds K).toFunctor.op ⋙ D) ⟶ colimit D :=
  colimit.pre D (toOpenNhds K).toFunctor.op

/-- Reindexing a colimit over all open neighbourhoods by compact-open neighbourhoods gives an
isomorphism. -/
@[stacks 0A3D "compact-open neighbourhood colimit reindexing"]
theorem colimitComparison_isIso [PrespectralSpace X] [QuasiSeparatedSpace X]
    (D : K.openNhdsᵒᵖ ⥤ C) [HasColimit D] :
    IsIso (colimitComparison K D) := sorry

/-- The compact-open colimit comparison carries each structure map to the corresponding
all-open structure map. -/
@[reassoc, stacks 0A3D "compact-open neighbourhood colimit structure map"]
theorem ι_comp_colimitComparison
    (D : K.openNhdsᵒᵖ ⥤ C) [HasColimit D]
    [HasColimit ((toOpenNhds K).toFunctor.op ⋙ D)]
    (U : K.compactOpenNhdsᵒᵖ) :
    colimit.ι ((toOpenNhds K).toFunctor.op ⋙ D) U ≫ colimitComparison K D =
      colimit.ι D ((toOpenNhds K).toFunctor.op.obj U) := sorry

end CompactOpenNhds

end TopologicalSpace.Compacts
