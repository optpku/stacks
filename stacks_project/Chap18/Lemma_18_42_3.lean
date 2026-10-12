/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Flat
import StacksCheckRecall

/-!
# Flat sections of a constant module sheaf

The shared owner packages the result sectionwise and as a property of the
whole `ModuleCat`-valued sheaf.
-/

@[expose] public section

/- Lemma 18.42.3 (093L): over a coherent ring, every section module of the
constant sheaf of a flat module is flat. -/
@[stacks 093L]
#check (@CategoryTheory.Sheaf.constant_app_flat)

/- The reusable all-objects formulation. -/
#check (@CategoryTheory.Sheaf.constant_sectionwiseFlat)
