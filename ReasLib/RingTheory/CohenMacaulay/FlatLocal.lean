/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module.RegularSequence
public import ReasLib.RingTheory.KrullDimension.Integral
public import ReasLib.RingTheory.Sequence.Regularity.BaseChange

/-!
# Cohen--Macaulayness under flat local base change

The API is organized around the local algebra-map owner `RingHom.Flat`.
Finite flatness gives the dimension-preserving special case, while the
dimension inequality criterion is independent of finite generation.
-/

@[expose] public section

universe u v

namespace RingHom.Flat

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S]
variable [IsLocalHom (algebraMap R S)]

/-- Lemma 10.112.9 (2) (Stacks tag `00R5`): a finite flat local algebra map
preserves Krull dimension. -/
@[stacks 00R5 "finite flat local dimension equality"]
theorem ringKrullDim_eq_of_finite [Module.Finite R S] [Module.Flat R S] :
    ringKrullDim R = ringKrullDim S := sorry

/-- Lemma 10.112.9 (1) (Stacks tag `00R5`): a finite flat local algebra over
a Cohen--Macaulay local ring is Cohen--Macaulay. -/
@[stacks 00R5 "Cohen--Macaulayness under finite flat local base change"]
theorem cohenMacaulay_of_finite [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite R S] [Module.Flat R S] [Module.CohenMacaulay R R] :
    Module.CohenMacaulay S S := sorry

variable [IsNoetherianRing R] [IsNoetherianRing S]

/-- Lemma 10.112.9 (3) (Stacks tag `00R5`): flat local base change of a
Cohen--Macaulay local ring is Cohen--Macaulay when the target dimension is no
larger than the source dimension. -/
@[stacks 00R5 "Cohen--Macaulayness under a dimension bound"]
theorem cohenMacaulay_of_ringKrullDim_le
    [Module.Flat R S] [Module.CohenMacaulay R R]
    (hdim : ringKrullDim S ≤ ringKrullDim R) :
    Module.CohenMacaulay S S := sorry

/-- Lemma 10.112.9 (4) (Stacks tag `00R5`): under the same hypotheses as
`cohenMacaulay_of_ringKrullDim_le`, the two Krull dimensions are equal. -/
@[stacks 00R5 "dimension equality under Cohen--Macaulay flat base change"]
theorem ringKrullDim_eq_of_ringKrullDim_le_of_cohenMacaulay
    [Module.Flat R S] [Module.CohenMacaulay R R]
    (hdim : ringKrullDim S ≤ ringKrullDim R) :
    ringKrullDim R = ringKrullDim S := sorry

end RingHom.Flat
