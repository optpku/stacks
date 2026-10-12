/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.RingHom.IndEtale.FormallyEtale
public import ReasLib.RingTheory.Smooth.Adic.Topology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal etaleness of henselization maps

The structural maps of henselizations and strict henselizations are ind-etale. This leaf records
their formal-etale and adic formal-smooth consequences.

@stack 07QN
-/

@[expose] public section

open IsLocalRing

universe u v

namespace IsHenselizationOf

variable {R : Type u} {S : Type v} [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- Lemma 15.45.2: the structural map of a henselization is formally etale. -/
@[stacks 07QN "formally etale henselization map"]
theorem formallyEtale : (algebraMap R S).FormallyEtale := sorry

/-- Lemma 15.45.2: the structural map of a henselization is formally smooth for the target
maximal-ideal-adic topology. -/
@[stacks 07QN "adic formal smoothness of a henselization map"]
theorem formallySmoothForMaximalIdeal :
    (algebraMap R S).formally_smooth_for_adic (maximalIdeal S) := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

variable {R : Type u} {S : Type v} [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- Lemma 15.45.2: the structural map of a strict henselization is formally etale. -/
@[stacks 07QN "formally etale strict-henselization map"]
theorem formallyEtale : (algebraMap R S).FormallyEtale := sorry

/-- Lemma 15.45.2: the structural map of a strict henselization is formally smooth for the
target maximal-ideal-adic topology. -/
@[stacks 07QN "adic formal smoothness of a strict-henselization map"]
theorem formallySmoothForMaximalIdeal :
    (algebraMap R S).formally_smooth_for_adic (maximalIdeal S) := sorry

end IsStrictHenselizationOf
