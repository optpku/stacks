/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.StageTower

/-!
# Isomorphism transport for filtration-stage towers

An isomorphism of filtered complexes induces an isomorphism on every component of the integer
stage tower and hence on the whole natural transformation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.StageTower

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {K L : FilteredComplex C}

/-- Every component of a tower map is an isomorphism when the filtered-complex map is. -/
@[stacks 012L "isomorphism on integer filtration-stage tower components"]
noncomputable instance map_app_isIso (f : K ⟶ L) (i : ℤᵒᵖ) [IsIso f] :
    IsIso ((map f).app i) := sorry

/-- A map of integer filtration-stage towers is an isomorphism when its filtered-complex map is. -/
@[stacks 012L "isomorphism of integer filtration-stage tower maps"]
noncomputable instance map_isIso (f : K ⟶ L) [IsIso f] : IsIso (map f) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso ((map f).app (Opposite.op 0))
#synth IsIso (map f)

end CategoryTheory.FilteredComplex.StageTower
