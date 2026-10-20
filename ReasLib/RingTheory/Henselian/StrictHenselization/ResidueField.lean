/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.LocalRing.ResidueField.Model

@[expose] public section

/-!
# Residue-field models of strict henselizations

A strict henselization has a residue field that realizes a separable closure
of the base residue field.  This leaf exposes that fact in the map-oriented
`IsLocalRing.ResidueField.LocalModel` language, without choosing a realization
as public data.

@stack 04GP
-/

universe u v w

namespace IsStrictHenselizationOf

section

variable {R : Type u} {S : Type v} {K : Type w}
variable [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
variable [IsStrictHenselizationOf R S] [Field K]

namespace ResidueField

/-- Tag 04GP: the residue-field map of a strict henselization has separable
closure target.  This is stated in the map-oriented language used by
`RingHom.SeparableClosure.Realization`. -/
@[stacks 04GP "strict-henselization residue field is a separable closure"]
theorem map_isSepClosure :
    RingHom.IsSepClosure (IsLocalRing.ResidueField.map (algebraMap R S)) := sorry

/-- The residue field of a strict henselization realizes the relative
separable closure of every map from the base residue field into a separably
closed field.  The realization is asserted only existentially, because it is
not canonical.  The tensor-product construction of Stacks Lemma 10.156.6 is
one downstream use. -/
@[stacks 04GP "residue-field model of a strict henselization"]
theorem existsModel
    [IsSepClosed K]
    (baseMap : IsLocalRing.ResidueField R →+* K) :
    ∃ model : IsLocalRing.ResidueField.LocalModel (K := K) (algebraMap R S),
      model.residueMap = baseMap := sorry

end ResidueField

end

end IsStrictHenselizationOf
