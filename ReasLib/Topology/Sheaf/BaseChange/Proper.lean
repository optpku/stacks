/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Maps.Proper.Characterization
public import ReasLib.Topology.Sheaf.Notation
public import ReasLib.Topology.Sheaves.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Proper base change for set-valued sheaves

This leaf adds the properness theorem to the coefficient-generic base-change transformation.
The square is an arbitrary cartesian square of spaces; no chosen pullback object or topos-level
wrapper is part of the public API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory TopCat

noncomputable section

universe u

namespace TopCat.Sheaf.BaseChange

/-- Lemma 20.18.3 (Proper base change for sheaves of sets) (0D90): for a cartesian square of
topological spaces whose original vertical map is proper, the set-valued sheaf base-change
component `g⁻¹ f_* ℱ ⟶ f'_* (g')⁻¹ ℱ` is an isomorphism. -/
@[stacks 0D90 "proper base change for sheaves of sets"]
theorem map_app_isIso_of_proper
    {X X' Y Y' : TopCat.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hcart : IsPullback g' f' f g) (hf : IsProperMap f) (ℱ : Sh(X)) :
    IsIso ((map (Type u) hcart.toCommSq).app ℱ) := sorry

/-- The set-valued sheaf base-change transformation for a proper cartesian square is a natural
isomorphism. -/
@[stacks 0D90 "functorial proper base change for sheaves of sets"]
theorem map_isIso_of_proper
    {X X' Y Y' : TopCat.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hcart : IsPullback g' f' f g) (hf : IsProperMap f) :
    IsIso (map (Type u) hcart.toCommSq) := sorry

end TopCat.Sheaf.BaseChange
