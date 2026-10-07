module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.IntegralClosure

/-!
@stack 092X
-/

@[expose] public section

open IsLocalRing

universe u v

/- Lemma 15.105.23 (1): the domain target of an integral homomorphism from a
henselian local ring is henselian local. -/
@[stacks 092X "Lemma 15.105.23 (1)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [HenselianLocalRing A] (f : A →+* B) (hf : f.IsIntegral)
    [IsDomain B] ↦
  (hf.henselianLocalRing : HenselianLocalRing B)

/- Lemma 15.105.23 (2): under the same hypotheses, the homomorphism `f` is
local. -/
@[stacks 092X "Lemma 15.105.23 (2)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [HenselianLocalRing A] (f : A →+* B) (hf : f.IsIntegral)
    [IsDomain B] ↦
  (hf.isLocalHom_of_henselian : IsLocalHom f)

/- Lemma 15.105.23 (3): the domain target of an integral homomorphism from a
strictly henselian local ring is strictly henselian local. -/
@[stacks 092X "Lemma 15.105.23 (3)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [StrictHenselianLocalRing A] (f : A →+* B) (hf : f.IsIntegral)
    [IsDomain B] ↦
  (hf.strictHenselianLocalRing : StrictHenselianLocalRing B)

/- Lemma 15.105.23 (4): under the common integral-domain hypotheses, the
induced residue-field extension is purely inseparable when `A` is strictly
henselian. -/
-- This is the one justified source-level instance pin: the base ring is fixed
-- by `f`, but cannot be recovered from an instance head on `B`, so the general
-- transfer theorem must not be registered globally.
@[stacks 092X "Lemma 15.105.23 (4)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [StrictHenselianLocalRing A] (f : A →+* B) (hf : f.IsIntegral)
    [IsDomain B] ↦
  letI : HenselianLocalRing B :=
    hf.henselianLocalRing
  hf.residueFieldMap_isPurelyInseparable hf.isLocalHom_of_henselian
