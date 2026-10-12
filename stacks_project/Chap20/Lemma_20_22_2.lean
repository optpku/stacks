/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.HigherDirectImage.Stalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Lemma 20.22.2 (0A3E): for a spectral map of spectral spaces, the canonical map from the stalk
of `R^p f_* F` at `y` to degree-`p` cohomology on `f⁻¹(nhdsKer {y})` is an isomorphism. -/
@[stacks 0A3E]
#check fun {X Y : TopCat.{u}} [SpectralSpace X] [SpectralSpace Y]
    (f : X ⟶ Y) (hf : IsSpectralMap f) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) ↦
  TopCat.Sheaf.HigherDirectImage.Stalk.comparison_isIso f hf y F p

#check @TopCat.Sheaf.HigherDirectImage.Stalk.comparison
#check @TopCat.Sheaf.HigherDirectImage.Stalk.stageMap_comp_comparison
#check @TopCat.Sheaf.HigherDirectImage.Stalk.comparison_map
#check @TopCat.Sheaf.HigherDirectImage.Stalk.cohomologyIso
#check @TopCat.Sheaf.HigherDirectImage.Presheaf.iso
