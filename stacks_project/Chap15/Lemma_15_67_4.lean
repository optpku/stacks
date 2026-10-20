/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.FlatRepresentative

/-!
# Lower-bounded flat representatives

This file is the source-facing recall for Lemma 15.67.4.

@stack 0BYL
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.67.4: an object `K` of `D(R)` has Tor-amplitude in `[a, ∞]` if and only if it is
quasi-isomorphic to a K-flat cochain complex of flat `R`-modules supported in degrees `≥ a`. -/
@[stacks 0BYL "Lemma 15.67.4"]
#check fun {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) (a : ℤ) ↦
  (Iff.trans (DerivedCategory.hasTorAmplitudeGE_iff_hasFlatRepresentativeGE K a)
      (DerivedCategory.hasFlatRepresentativeGE_iff K a) :
    DerivedCategory.HasTorAmplitudeGE R K a ↔
      ∃ (E : CochainComplex (ModuleCat R) ℤ) (_ : K ≅ DerivedCategory.Q.obj E),
        E.IsStrictlyGE a ∧ E.IsKFlat ∧ HomologicalComplex.IsTermwiseFlat E)

#check @DerivedCategory.HasFlatRepresentativeGE

#check @DerivedCategory.hasFlatRepresentativeGE_iff

#check @DerivedCategory.HasTorAmplitudeGE.hasFlatRepresentativeGE

#check @DerivedCategory.HasFlatRepresentativeGE.hasTorAmplitudeGE
