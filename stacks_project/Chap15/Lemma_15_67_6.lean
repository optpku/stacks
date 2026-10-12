/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.FlatResolution

/-!
# Lemma 15.67.6

@stack 066F
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.67.6 (1), tag `066F`: an `R`-module has Tor dimension at most `d` exactly when it has a
finite flat resolution of length at most `d`. -/
@[stacks 066F "Lemma 15.67.6 (1)"]
#check fun {R : Type u} [CommRing R] (M : ModuleCat R) (d : ℕ) ↦
  (ModuleCat.hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE M d :
    DerivedCategory.DerivedTensor.HasTorDimensionLE M d ↔
      ModuleCat.HasFiniteFlatResolutionLengthLE M d)

/- Lemma 15.67.6 (2): Tor dimension at most zero is flatness. -/
@[stacks 066F "Lemma 15.67.6 (2)"]
#check fun {R : Type u} [CommRing R] (M : ModuleCat R) ↦
  (ModuleCat.hasTorDimensionLE_zero_iff_flat M :
    DerivedCategory.DerivedTensor.HasTorDimensionLE M 0 ↔ Module.Flat R M)
