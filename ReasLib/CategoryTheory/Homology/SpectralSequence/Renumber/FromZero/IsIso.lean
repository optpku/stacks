/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.IsIso
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage.IsIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport under standard renumbering from page zero
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.CohomologicalSpectralSequence.Renumber.FromZero

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The standard renumbering from page zero preserves isomorphisms. -/
@[stacks 0G1Y "isomorphism transport under renumbering from page zero", stacks 0G20]
noncomputable instance map_isIso
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E') [IsIso f] :
    IsIso (map f) := sorry

/-- Every page map of a renumbered isomorphism from page zero is an isomorphism. -/
@[stacks 0G1Y "page isomorphism under renumbering from page zero", stacks 0G20]
noncomputable instance map_hom_isIso
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E')
    (r : ℤ) (hr : 2 ≤ r) [IsIso f] :
    IsIso ((map f).hom r hr) := sorry

/-- Every entry map of a renumbered isomorphism from page zero is an isomorphism. -/
@[stacks 0G1Y "entry isomorphism under renumbering from page zero", stacks 0G20]
noncomputable instance map_f_isIso
    {E E' : CohomologicalSpectralSequence C 0} (f : E ⟶ E')
    (r : ℤ) (hr : 2 ≤ r) (ij : ℤ × ℤ) [IsIso f] :
    IsIso (((map f).hom r hr).f ij) := sorry

variable {E E' : CohomologicalSpectralSequence C 0}
variable (f : E ⟶ E') [IsIso f]

#synth IsIso (map f)
#synth IsIso ((map f).hom 2 le_rfl)
#synth IsIso (((map f).hom 2 le_rfl).f (0, 0))

end CategoryTheory.CohomologicalSpectralSequence.Renumber.FromZero
