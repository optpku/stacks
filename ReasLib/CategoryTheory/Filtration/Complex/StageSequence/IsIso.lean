/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.StageSequence

/-!
# Isomorphism transport for selected filtration-stage sequences

An isomorphism of filtered complexes induces an isomorphism on every component of an antitone
stage sequence and hence on the whole natural transformation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.StageSequence

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {K L : FilteredComplex C}

/-- Every component of a selected stage-sequence map is an isomorphism when the filtered-complex
map is. -/
@[stacks 0D8Z "isomorphism on antitone filtration-stage sequence components"]
noncomputable instance map_app_isIso (f : K ⟶ L) (p : ℕ → ℤ) (hp : Antitone p) (n : ℕ)
    [IsIso f] : IsIso ((map f p hp).app n) := sorry

/-- A selected stage-sequence map is an isomorphism when its filtered-complex map is. -/
@[stacks 0D8Z "isomorphism of antitone filtration-stage sequence maps"]
noncomputable instance map_isIso (f : K ⟶ L) (p : ℕ → ℤ) (hp : Antitone p)
    [IsIso f] : IsIso (map f p hp) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso ((map f (fun _ ↦ (0 : ℤ)) (fun _ _ _ ↦ le_rfl)).app 0)
#synth IsIso (map f (fun _ ↦ (0 : ℤ)) (fun _ _ _ ↦ le_rfl))

end CategoryTheory.FilteredComplex.StageSequence
