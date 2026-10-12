/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect modules after flat scalar extension

@stack 066X

The degree-zero module form of perfect base change is kept beside the derived-object owner.  It
accepts an explicit flat ring homomorphism and exposes only the proposition needed by downstream
module arguments.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Lemma 15.75.10 (Stacks `066X`): a flat scalar extension sends perfect modules to perfect
modules. -/
@[stacks 066X "perfect modules after flat scalar extension"]
theorem IsPerfect.extendScalars
    (f : R →+* S) (hf : f.Flat) {M : ModuleCat R} (hM : M.IsPerfect) :
    ModuleCat.IsPerfect ((ModuleCat.extendScalars f).obj M) := sorry

end CategoryTheory.ModuleCat
