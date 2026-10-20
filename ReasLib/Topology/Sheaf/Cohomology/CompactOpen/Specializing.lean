module

public import ReasLib.Topology.CompactOpen.Neighborhood
public import ReasLib.Topology.Constructible.Retrocompact
public import ReasLib.Topology.Sheaf.Cohomology.CompactOpen.Difference
public import ReasLib.Topology.Sheaf.Cohomology.CompactOpen.Intersection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology near a compact subset of a spectral space

This leaf specializes the generic compact-open intersection comparisons to the canonical
compact-open neighbourhoods of a compact subset.  Compact subsets remain bundled as `Compacts`,
while companion theorems retain the set-and-property form used by source statements.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology
open CategoryTheory.Limits

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology.CompactOpen.Specializing

variable {X : TopCat.{u}}

/-- The cohomology diagram on the compact-open neighbourhoods of a compact subset. -/
@[stacks 0A3D "compact-open neighbourhood cohomology diagram"]
abbrev diagram (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (K.compactOpenNhds)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  Intersection.diagram K.compactOpenNhds F p

/-- Cohomology of the restriction to the points specializing to a compact subset. -/
@[stacks 0A3D "specializing-subset cohomology target"]
abbrev target (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    AddCommGrpCat.{u} :=
  Intersection.target (nhdsKer (K : Set X)) F p

/-- The canonical comparison from neighbourhood cohomology to cohomology on the specializing
subset. -/
@[stacks 0A3D "specializing-subset cohomology comparison"]
noncomputable def comparison [PrespectralSpace X] [QuasiSeparatedSpace X]
    (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    colimit (diagram K F p) ⟶ target K F p :=
  Intersection.comparison
    (TopologicalSpace.Compacts.CompactOpenNhds.isDirectedIntersection K) F p

/-- Lemma 20.22.1 (1) (0A3D): on a spectral space, the compact-open neighbourhood comparison
for a compact subset is an isomorphism in every degree. -/
@[stacks 0A3D "cohomology near a compact subset"]
theorem comparison_isIso [SpectralSpace X]
    (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (comparison K F p) := sorry

/-- Lemma 20.22.1 (1), in the source-facing set-and-compactness form. -/
@[stacks 0A3D "cohomology near a compact subset, set form"]
theorem comparison_isIso_of_isCompact [SpectralSpace X]
    (F : X.Sheaf AddCommGrpCat.{u}) (E : Set X) (hE : IsCompact E) (p : ℕ) :
    IsIso (comparison (⟨E, hE⟩ : Compacts X) F p) := sorry

namespace Sdiff

/-- The cohomology diagram `U ↦ H^p(U \ K, F|_{Kᶜ})` on compact-open neighbourhoods of
`K`. -/
@[stacks 0A3D "compact-open neighbourhood-difference cohomology diagram"]
abbrev diagram (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (K.compactOpenNhds)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  Difference.diagram K.compactOpenNhds (K : Set X) F p

/-- Cohomology of the restriction to the points specializing to `K` but not lying in `K`. -/
@[stacks 0A3D "specializing-subset difference cohomology target"]
abbrev target (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    AddCommGrpCat.{u} :=
  Difference.target (nhdsKer (K : Set X)) (K : Set X) F p

/-- The canonical comparison from neighbourhood-difference cohomology to cohomology on
`nhdsKer K \ K`. -/
@[stacks 0A3D "specializing-subset difference cohomology comparison"]
noncomputable def comparison [PrespectralSpace X] [QuasiSeparatedSpace X]
    (K : Compacts X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    colimit (diagram K F p) ⟶ target K F p :=
  Difference.comparison
    (TopologicalSpace.Compacts.CompactOpenNhds.isDirectedIntersection K) (K : Set X) F p

/-- Lemma 20.22.1 (2) (0A3D): if the compact subset is constructible, its
neighbourhood-difference comparison is an isomorphism in every degree. -/
@[stacks 0A3D "cohomology near a constructible subset, off the subset"]
theorem comparison_isIso [SpectralSpace X]
    (K : Compacts X) (hK : IsConstructible (K : Set X))
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (comparison K F p) := sorry

/-- Lemma 20.22.1 (2), in the source-facing constructible-set form. -/
@[stacks 0A3D "cohomology near a constructible subset, set form"]
theorem comparison_isIso_of_isConstructible [SpectralSpace X]
    (F : X.Sheaf AddCommGrpCat.{u}) (E : Set X) (hE : IsConstructible E) (p : ℕ) :
    IsIso (comparison hE.toCompacts F p) := sorry

end Sdiff

end TopCat.Sheaf.Cohomology.CompactOpen.Specializing
