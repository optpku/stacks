/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Cohomology of Filtered Complexes

This is the cochain-facing bridge for the general `HomologicalComplex.Filtered.Homology` API.
The general owner handles arbitrary complex shapes; the names in this file retain the notation
used by filtered cochain-complex consumers without reimplementing the construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜]

namespace FilteredComplex

section Cohomology

variable [CategoryWithHomology 𝒜]

/-- The map on degree-`n` cohomology induced by `K.stageInclusion p`. -/
@[stacks 012P "stagewise cohomology map"]
noncomputable abbrev cohomologyMap (K : FilteredComplex 𝒜) (p n : ℤ) :
    (K.stage p).homology n ⟶ K.underlying.homology n :=
  HomologicalComplex.Filtered.Homology.map K p n

/-- For `p ≤ q`, the cohomology map from the `q`-th stage factors through that from the
`p`-th stage. -/
@[stacks 012P "factorization of stagewise cohomology maps"]
theorem cohomologyMap_factorization (K : FilteredComplex 𝒜) {p q n : ℤ} (hpq : p ≤ q) :
    K.cohomologyMap q n =
      HomologicalComplex.homologyMap (K.stageComparison hpq) n ≫ K.cohomologyMap p n := sorry

/-- Stagewise cohomology maps commute with every morphism of filtered cochain complexes. -/
@[reassoc, stacks 012P "naturality of stagewise cohomology maps"]
theorem cohomologyMap_naturality {K L : FilteredComplex 𝒜} (f : K ⟶ L) (p n : ℤ) :
    HomologicalComplex.homologyMap (K.stageMap f p) n ≫ L.cohomologyMap p n =
      K.cohomologyMap p n ≫ HomologicalComplex.homologyMap (K.underlyingMap f) n := sorry

end Cohomology

section Filtration

variable [HasImages 𝒜] [CategoryWithHomology 𝒜]

/-- The images of the stagewise cohomology maps form a decreasing family of subobjects. -/
@[stacks 012P "monotonicity of the induced cohomology filtration"]
theorem inducedCohomologyFiltration_antitone (K : FilteredComplex 𝒜) (n : ℤ) :
    Antitone (fun p : ℤ ↦ imageSubobject (K.cohomologyMap p n)) := sorry

/-- Definition 12.24.5: the decreasing filtration on `K.underlying.homology n` whose `p`-th
stage is the image of `K.cohomologyMap p n`. -/
@[stacks 012P]
noncomputable abbrev inducedCohomologyFiltration (K : FilteredComplex 𝒜) (n : ℤ) :
    DecreasingFiltration (K.underlying.homology n) :=
  HomologicalComplex.Filtered.Homology.Filtration.induced K n

/-- The `p`-th stage of the induced cohomology filtration is the image of the cohomology map
from the `p`-th filtration stage. -/
@[stacks 012P "stage formula for the induced cohomology filtration"]
theorem inducedCohomologyFiltration_obj (K : FilteredComplex 𝒜) (n p : ℤ) :
    (K.inducedCohomologyFiltration n).stage p = imageSubobject (K.cohomologyMap p n) := sorry

namespace Cohomology.Filtration

/-- The induced cohomology filtrations are exhaustive in every degree.  This is the cochain
bridge to the shape-independent induced-homology filtration property. -/
@[stacks 012U "exhaustive induced cohomology filtrations"]
abbrev IsExhaustive (K : FilteredComplex 𝒜) : Prop :=
  HomologicalComplex.Filtered.Homology.Filtration.IsExhaustive K

section ZeroObject

variable [HasZeroObject 𝒜]

/-- The induced cohomology filtrations are separated in every degree. -/
@[stacks 012U "separated induced cohomology filtrations"]
abbrev IsSeparated (K : FilteredComplex 𝒜) : Prop :=
  HomologicalComplex.Filtered.Homology.Filtration.IsSeparated K

/-- The induced cohomology filtrations are separated and exhaustive in every degree. -/
@[stacks 012U "separated and exhaustive induced cohomology filtrations"]
abbrev IsSeparatedExhaustive (K : FilteredComplex 𝒜) : Prop :=
  HomologicalComplex.Filtered.Homology.Filtration.IsSeparatedExhaustive K

/-- The induced cohomology filtrations are finite in every degree. -/
@[stacks 012U "finite induced cohomology filtrations"]
abbrev IsFinite (K : FilteredComplex 𝒜) : Prop :=
  HomologicalComplex.Filtered.Homology.Filtration.IsFinite K

end ZeroObject

section Complete

variable [HasCokernels 𝒜]

/-- The induced cohomology filtrations are complete in every degree. -/
@[stacks 012U "complete induced cohomology filtrations"]
abbrev IsComplete (K : FilteredComplex 𝒜) : Prop :=
  HomologicalComplex.Filtered.Homology.Filtration.IsComplete K

end Complete

end Cohomology.Filtration

end Filtration

end FilteredComplex

end CategoryTheory
