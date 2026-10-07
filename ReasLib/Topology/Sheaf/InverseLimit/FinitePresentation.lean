module

public import ReasLib.Topology.Sheaf.Presentation
public import ReasLib.Topology.Sheaves.InverseLimit.PullbackSections
public import ReasLib.Topology.Spectral.FinitePresentation
public import ReasLib.Topology.Spectral.Limit.CompactOpens
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentations of sheaves on spectral spaces

This file connects finite presentations by compact-open sheaf generators with finite stages of a
spectral inverse-limit presentation. The presentation property is expressed through the generic
site-level finite-coequalizer API; finite lower-shriek constant fibres are recovered by expanding
them into finite coproducts of representable generators.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped TopCat

noncomputable section

universe u

namespace TopCat.Sheaf.CompactOpenPresentation

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/-- Lemma 17.19.3 (0CAK): a finitely compact-open-presented set-valued sheaf on a spectral space
descends along a spectral map to a sheaf with finite stalks on a finite sober space. -/
@[stacks 0CAK]
theorem IsFinite.existsFiniteSoberModel [SpectralSpace X] {F : X.Sheaf (Type u)}
    (hF : IsFinite F) :
    ∃ (Y : TopCat.{u}) (_ : Finite Y) (_ : T0Space Y ∧ QuasiSober Y) (f : X ⟶ Y)
      (_ : IsSpectralMap f) (G : Y.Sheaf (Type u)) (_ : ((f⁻¹).obj G) ≅ F),
      ∀ y : Y, Finite (G.presheaf.stalk y) := sorry

end TopCat.Sheaf.CompactOpenPresentation
