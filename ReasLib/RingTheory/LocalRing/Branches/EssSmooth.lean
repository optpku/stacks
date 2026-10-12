/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import ReasLib.RingTheory.LocalRing.Branches
public import ReasLib.RingTheory.Smooth.AtPrime.ClosedPoint
public import ReasLib.RingTheory.Smooth.EssSmooth
import Mathlib.Tactic.CrossRefAttribute

/-!
# Branch numbers under essentially smooth local maps

This file records invariance of ordinary and geometric branch numbers under a local map that is a
localization of a smooth ring map. The map-first hypotheses keep both essential smoothness and the
residue-field extension attached to the structural map.
@stack 0DQ1
-/

@[expose] public section

open IsLocalRing

universe u v w x

namespace RingHom.EssSmooth

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- Geometric branch number is invariant under an essentially smooth local map. -/
@[stacks 0DQ1 "geometric branches under an essentially smooth local map"]
theorem geometricBranchNumber_eq
    {Ash : Type w} {Bsh : Type x}
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [CommRing Bsh] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    (h : (algebraMap A B).EssSmooth) :
    geometricBranchNumber A Ash = geometricBranchNumber B Bsh := sorry

/-- Branch number is invariant under an essentially smooth local map whose residue-field map is
purely inseparable. -/
@[stacks 0DQ1 "branches under an essentially smooth local map"]
theorem branchNumber_eq_of_residuePurelyInseparable
    {Ah : Type w} {Bh : Type x}
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    [CommRing Bh] [Algebra B Bh] [IsHenselizationOf B Bh]
    (h : (algebraMap A B).EssSmooth)
    (hκ : (ResidueField.map (algebraMap A B)).IsPurelyInseparable) :
    branchNumber A Ah = branchNumber B Bh := sorry

end RingHom.EssSmooth
