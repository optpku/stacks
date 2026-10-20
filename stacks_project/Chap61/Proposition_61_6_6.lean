/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski.Refinement
import StacksCheckRecall

/-!
# Proposition 61.6.6

A ring map that identifies local rings admits a faithfully flat ind-Zariski
extension whose composite is ind-Zariski.
-/

@[expose] public section

universe u

open Algebra.WLocalHull

#check (RingHom.IndZariski.wLocalization_comp :
  ∀ {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B},
    f.IsIsoOnLocalRings →
      ((algebraMap B (wLocalization B)).comp f).IndZariski)

/- Proposition 61.6.6: a ring map identifying local rings admits a faithfully
flat ind-Zariski extension whose composite is ind-Zariski. -/
@[stacks 097G] #check (RingHom.IndZariski.exists_faithfullyFlat_of_isIsoOnLocalRings :
  ∀ {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B},
    f.IsIsoOnLocalRings →
    ∃ (B' : Type u) (_ : CommRing B') (g : B →+* B'),
      g.FaithfullyFlat ∧ g.IndZariski ∧ (g.comp f).IndZariski)
