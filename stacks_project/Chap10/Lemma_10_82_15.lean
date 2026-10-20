/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.UniversallyInjective.FaithfullyFlat

@[expose] public section

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-!
# Lemma 10.82.15

Lemma 10.82.15: a faithfully flat ring map `R → S` is universally injective as an `R`-linear
map, and contraction recovers every ideal.

@stack 05CK
-/

@[stacks 05CK "faithfully flat algebra maps are universally injective"]
#check @Module.FaithfullyFlat.universallyInjective_algebraLinearMap

/- The textbook corollary `R ∩ IS = I` is the canonical contraction statement
`(I.map (algebraMap R S)).comap (algebraMap R S) = I`. -/
@[stacks 05CK "faithfully flat ideal contraction"]
#check @Ideal.comap_map_eq_self_of_faithfullyFlat

end
