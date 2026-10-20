/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.Localization.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness in a Localized Tensor-Product Square

This leaf owns ascent and descent of module and algebra flatness when the
upper-right ring is a localization of the tensor-product pushout.  Local-ring
hypotheses occur only in the two descent statements, where they make the map
`S → S'` faithfully flat.

@stack 00MQ
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x y

section

variable {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
variable (W : Submonoid (S ⊗[R] R'))
variable [tensorAlgebra : Algebra (S ⊗[R] R') S']
variable [towerS : IsScalarTower S (S ⊗[R] R') S']
variable [towerR' : IsScalarTower R' (S ⊗[R] R') S']
variable [localization : IsLocalization W S']

include tensorAlgebra towerS towerR' localization

variable {M : Type y} [AddCommGroup M] [Module R M] [Module S M]
variable [IsScalarTower R S M]

namespace Module.Flat.LocalizationSquare

/-- Lemma 10.100.1 (1): flatness ascends across a localized tensor-product square. -/
@[stacks 00MQ "(1), module flatness ascent"]
theorem baseChange (hM : Module.Flat R M) :
    Module.Flat R' (S' ⊗[S] M) := sorry

/-- Lemma 10.100.1 (2): flatness descends across a localized tensor-product square when its
vertical target map is a local homomorphism of local rings and the base change is flat. -/
@[stacks 00MQ "(2), module flatness descent"]
theorem descend [IsLocalRing S] [IsLocalRing S'] [IsLocalHom (algebraMap S S')]
    (hM : Module.Flat R' (S' ⊗[S] M)) (hbase : (algebraMap R R').Flat) :
    Module.Flat R M := sorry

end Module.Flat.LocalizationSquare

namespace RingHom.Flat.LocalizationSquare

/-- Lemma 10.100.1 (3): algebra flatness ascends across a localized tensor-product square. -/
@[stacks 00MQ "(3), algebra flatness ascent"]
theorem baseChange (hsource : (algebraMap R S).Flat) :
    (algebraMap R' S').Flat := sorry

/-- Lemma 10.100.1 (4): algebra flatness descends across a localized tensor-product square when
its vertical target map is a local homomorphism of local rings and the base change is flat. -/
@[stacks 00MQ "(4), algebra flatness descent"]
theorem descend [IsLocalRing S] [IsLocalRing S'] [IsLocalHom (algebraMap S S')]
    (htarget : (algebraMap R' S').Flat) (hbase : (algebraMap R R').Flat) :
    (algebraMap R S).Flat := sorry

end RingHom.Flat.LocalizationSquare

end
