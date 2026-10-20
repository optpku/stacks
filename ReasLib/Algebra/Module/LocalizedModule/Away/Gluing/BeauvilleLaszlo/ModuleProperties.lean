/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Finite
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Replacement
public import ReasLib.RingTheory.Finiteness.Projective.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module properties over a Beauville--Laszlo glueing pair

Flatness and finite projectivity are detected after extension to the target
ring and localization away from the distinguished element.  The ring map is
kept explicit; the target-ring tensor product is formed using its associated
algebra structure only inside the theorem statements.

@stack 0BP7
@stack 0BP6
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace LocalizedModule.Away.BeauvilleLaszlo

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Lemma 15.91.18 (0BP7): over a Beauville--Laszlo glueing pair, a module is
flat exactly when its target-ring base change and its localization away from
the distinguished element are flat. -/
@[stacks 0BP7 "flat modules over a Beauville-Laszlo glueing pair"]
theorem flat_iff_baseChange_and_localizedAway_of_glueingPair
    (φ : R →+* S) (f : R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (hpair : IsBeauvilleLaszloGlueingPairAlong φ f) :
    let _ : Algebra R S := φ.toAlgebra
    Module.Flat R M ↔
      Module.Flat S (S ⊗[R] M) ∧
        Module.Flat (Localization.Away f) (LocalizedModule.Away f M) := sorry

/-- Lemma 15.91.19 (0BP6): over a Beauville--Laszlo glueing pair, a module is
finite projective exactly when its target-ring base change and its
localization away from the distinguished element are finite projective. -/
@[stacks 0BP6, stacks 0BP8
  "finite projective modules over a Beauville-Laszlo glueing pair"]
theorem finiteProjective_iff_baseChange_and_localizedAway_of_glueingPair
    (φ : R →+* S) (f : R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (hpair : IsBeauvilleLaszloGlueingPairAlong φ f) :
    let _ : Algebra R S := φ.toAlgebra
    Module.FiniteProjective R M ↔
      Module.FiniteProjective S (S ⊗[R] M) ∧
        Module.FiniteProjective
          (Localization.Away f) (LocalizedModule.Away f M) := sorry

end LocalizedModule.Away.BeauvilleLaszlo
