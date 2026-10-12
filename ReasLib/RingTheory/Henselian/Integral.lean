/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselian
public import ReasLib.RingTheory.RingHom.Local.Integral
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Integral domain extensions of henselian local rings

The core API accepts an arbitrary integral ring homomorphism.  Algebra-map
specializations keep the base ring explicit because a target may carry many
algebra structures.  None of these transfers is a global instance: the source
map and base ring cannot be recovered from the target class head.

@stack 092X
-/

universe u v

namespace RingHom.IsIntegral

/-- The domain target of an integral homomorphism from a henselian local ring
is henselian local. -/
@[stacks 092X "integral domain targets of henselian local rings"]
theorem henselianLocalRing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [HenselianLocalRing R] [IsDomain S] {f : R →+* S}
    (hf : f.IsIntegral) : HenselianLocalRing S := sorry
-- Proof strategy: present `S` as the filtered direct limit of its finite adjoin subalgebras,
-- make each finite domain stage henselian local, prove the transition maps local, and transport
-- the direct-limit henselian structure to `S`.

/-- An integral homomorphism from a henselian local ring to a domain is
local. -/
@[stacks 092X "integral homomorphisms from henselian local rings to domains are local"]
theorem isLocalHom_of_henselian
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [HenselianLocalRing R] [IsDomain S] {f : R →+* S}
    (hf : f.IsIntegral) : IsLocalHom f := sorry
-- Proof strategy: install `hf.henselianLocalRing` on `S` and apply
-- `RingHom.IsIntegral.isLocalHom_of_isLocalRing`.

/-- The domain target of an integral homomorphism from a strictly henselian
local ring is strictly henselian local. -/
@[stacks 092X "integral domain targets of strictly henselian local rings"]
theorem strictHenselianLocalRing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [StrictHenselianLocalRing R] [IsDomain S] {f : R →+* S}
    (hf : f.IsIntegral) : StrictHenselianLocalRing S := sorry
-- Proof strategy: obtain henselian locality from `hf.henselianLocalRing`, use
-- `hf.residueFieldMap_isPurelyInseparable hf.isLocalHom_of_henselian`, and transfer separable
-- closedness across the resulting algebraic residue-field extension.

end RingHom.IsIntegral

namespace HenselianLocalRing

/-- An integral domain algebra over a henselian local ring is henselian
local. -/
@[stacks 092X "integral domain extensions of henselian local rings"]
theorem of_isIntegral
    (R : Type u) {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [HenselianLocalRing R] [Algebra.IsIntegral R S]
    [IsDomain S] : HenselianLocalRing S := sorry
-- Proof strategy: apply `RingHom.IsIntegral.henselianLocalRing` to `algebraMap R S` and
-- `Algebra.IsIntegral.isIntegral`.

/-- The algebra map to an integral domain algebra over a henselian local ring
is local. -/
@[stacks 092X "locality of integral domain extensions of henselian local rings"]
theorem isLocalHom_of_isIntegral
    (R : Type u) {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [HenselianLocalRing R] [Algebra.IsIntegral R S]
    [IsDomain S] : IsLocalHom (algebraMap R S) := sorry
-- Proof strategy: apply `RingHom.IsIntegral.isLocalHom_of_henselian` to the algebra map.

end HenselianLocalRing

namespace StrictHenselianLocalRing

/-- An integral domain algebra over a strictly henselian local ring is
strictly henselian local. -/
@[stacks 092X "integral domain extensions of strictly henselian local rings"]
theorem of_isIntegral
    (R : Type u) {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [StrictHenselianLocalRing R] [Algebra.IsIntegral R S]
    [IsDomain S] : StrictHenselianLocalRing S := sorry
-- Proof strategy: apply `RingHom.IsIntegral.strictHenselianLocalRing` to the algebra map.

end StrictHenselianLocalRing
