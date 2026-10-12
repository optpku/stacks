/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Local.Properties
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 61.3.1 (1): a ring map `φ : A → B` is a local isomorphism if for every
prime `q` of `B` there exists `g ∉ q` such that `A → Localization.Away g` induces an
open immersion `Spec (Localization.Away g) ⟶ Spec A`. -/
@[stacks 096E] #check (RingHom.IsLocalIso :
  ∀ {A B : Type u}, [CommRing A] → [CommRing B] → (A →+* B) → Prop)

/- Definition 61.3.1 (2): a ring map `φ : A → B` identifies local rings if for every
prime `q` of `B` the canonical map `Localization.localRingHom` at `φ⁻¹(q)` and `q`
is an isomorphism. -/
@[stacks 096E] #check (RingHom.IsIsoOnLocalRings :
  ∀ {A B : Type u}, [CommRing A] → [CommRing B] → (A →+* B) → Prop)
