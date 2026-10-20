/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import ReasLib.RingTheory.RingHom.IndEtale
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ind-etale local extensions realizing residue-field extensions

This leaf owns the local ind-etale producer for separable algebraic extensions
of a local ring's residue field.  Filtered-system presentations remain proof
infrastructure behind the map-level `RingHom.IndEtale` conclusion.

@stack 09E0
-/

@[expose] public section

universe u v

namespace IsLocalRing.ResidueField

/-- Lemma 10.159.2: every separable algebraic extension of a residue field is
realized by the residue field of a local ind-etale algebra. -/
@[stacks 09E0 "ind-etale local extension realizing a residue field"]
theorem exists_indEtale_localExtension
    {R : Type u} [CommRing R] [IsLocalRing R]
    (K : Type v) [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) K]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R'))
      (_ : IsLocalRing.ResidueField R' ≃ₐ[IsLocalRing.ResidueField R] K),
      (algebraMap R R').IndEtale := sorry

end IsLocalRing.ResidueField
